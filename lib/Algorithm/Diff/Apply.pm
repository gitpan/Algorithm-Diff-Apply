package Algorithm::Diff::Apply;
use Carp;
use strict;
use base qw{Exporter};
use vars qw{@EXPORT_OK $VERSION};
@EXPORT_OK = qw{apply_diff apply_diffs mark_conflicts};
$VERSION = '0.1.1';


# Apply a single diff sequence. Nice and simple, and doesn't require
# any pre-passes.

sub apply_diff
{
        my @ary = @{shift()};
        my $diff = shift;
        
        my $delta = 0;
        foreach my $hunk (@$diff)
        {
                foreach my $change (@$hunk)
                {
                        my ($op, $pos, $data) = @$change;
                        if ($op eq "-")
                        {
                                splice(@ary, $pos+$delta, 1);
                                --$delta;
			}
                        elsif ($op eq "+")
                        {
                                splice(@ary, $pos, 0, $data);
                                ++$delta;
                        }
                        else
                        {
                                die "unknown operation: \"$op\"\n";
                        }
                }
        }
        return wantarray ? @ary : \@ary;
}



# Apply one or more labelled diff sequences to a target array.
# Somewhat more complex; needs prepasses and consideration of
# conflicts.

sub apply_diffs
{
	# Collect args:
	my @ary = @{shift(@_)};
	my %opt;
	%opt = %{shift(@_)} if ref($_[0]) && (ref($_[0]) eq 'HASH');
	my %diffset;
	while (my $tag = shift)
	{
		ref($tag) and die("Tagnames must be scalar");
		my $diff = shift;
		ref($diff) eq 'ARRAY'
			or croak("Diff sequences must be references of type \"ARRAY\"");
		$diff = [__homogenise_diff(@$diff)];
		$diffset{$tag} = $diff;
	}

	# Trivial case
	if (scalar keys %diffset < 1)
	{
		return wantarray ? @ary : \@ary;
	}

	# Apply hunks one by one, and generate a new array.
	my $resolver = $opt{resolver} || \&mark_conflicts;
	my $delta = 0;
	while (my ($min, $max, %alts) = __shift_next_alternatives(\%diffset))
	{
		my @orig = @ary[$min + $delta .. $max + $delta - 1];
		my @replacement;

		my %alt_txts;
		foreach my $id (sort keys %alts)
		{
			my @tmp = @orig;
			my $tmp_delta = -$min;
			foreach my $hunk (@{ $alts{$id} })
			{
				__apply_hunk(\@tmp, \$tmp_delta, $hunk);
			}
			$alt_txts{$id} = \@tmp;
		}
		
		if (scalar keys %alt_txts == 1)
		{
			my ($r) = values %alt_txts;
			@replacement = @$r;
		}
		else
		{
			@replacement = $resolver->(src_range_end => $max,
						   src_range_start => $min,
						   src_range => \@orig,
						   alt_txts => \%alt_txts,
						   invoc_opts => \%opt);
		}		
		splice(@ary, $min + $delta, $#orig+1, @replacement);
		$delta += ($#replacement - $#orig);
	}

	return wantarray ? @ary : \@ary;
}



# The default conflict resolution subroutine. Returns all alternative
# texts with conflict markers inserted around them.

sub mark_conflicts
{
	my %opt = @_;
	my %alt = %{$opt{alt_txts}};
	my @ret;
	foreach my $id (sort keys %alt)
	{
		push @ret, ">>>>>> $id\n";
		push @ret, @{$alt{$id}};
	}
	push @ret, "<<<<<<\n";
	return @ret;
}



# *Terminology*
#
# A "diffset" is a hash of IDs whose values are arrays holding
# sequences of diffs generated from different sources. There may be
# conflicts within a diffset.
# 
# An "alternatives" diffset is a minimal diffset which contains no
# more than one conflict. I can't think of a better name for it, as
# there's a special case where it only consists of a single key
# pointing at a single hunk.


# Extracts the array ($min, $max, %alts) from %$diffset where $min and
# $max describe the range of lines affected by all the diff hunks in
# %alts, and %alts is a diffset containing at least one alternative.
# Returns an empty array if there are no diff hunks left.

sub __shift_next_alternatives
{
	my $diffset = shift;
	my $id = __next_hunk_id($diffset);
	defined($id) or return ();
	my ($cflict_max, $cflict_min);
	my %cflict;
	my $hunk = shift @{$diffset->{$id}};
	$cflict{$id} = [ $hunk ];

	# Seed range with $hunk:
	my @ch = @{$hunk->{changes}};
	my $span = grep { $_->[0] eq '-' } @ch;
	$cflict_min = $hunk->{start};
	$cflict_max = $cflict_min + $span;

	# Detect conflicting hunks, and add those in too.
	my %ignore;
	while (my $tmp_id = __next_hunk_id($diffset, %ignore))
	{
		my $tmp_hunk = $diffset->{$tmp_id}->[0];
		@ch = @{$tmp_hunk->{changes}};
		my $tmp_span = grep { $_->[0] eq '-' } @ch;
		my $tmp_max = $tmp_hunk->{start} + $tmp_span;
		if ($tmp_hunk->{start} <= $cflict_max)
		{
			exists $cflict{$tmp_id} or $cflict{$tmp_id} = [];
			shift @{$diffset->{$tmp_id}};
			push @{$cflict{$tmp_id}}, $tmp_hunk;
			$cflict_max = $tmp_max if $tmp_max > $cflict_max;
		}
		else
		{
			$ignore{$tmp_id} = 1;
		}
	}

	return ($cflict_min, $cflict_max, %cflict);
}


# Applies a hunk to an array, and calculates the lines lost or gained
# by doing so.

sub __apply_hunk
{
        my ($ary, $rdelta, $hunk) = @_;
	my $pos = $hunk->{start} + $$rdelta;
        foreach my $change (@{$hunk->{changes}})
        {
                if ($change->[0] eq '+')
                {
                        splice(@$ary, $pos, 0, $change->[1]);
                        ++$$rdelta;
                        ++$pos;
                }
                else
                {
                        splice(@$ary, $pos, 1);
                        --$$rdelta;
                }
        }
}


# Returns the ID of the hunk in %$diffset whose ->{start} is lowest,
# or undef. %ignore{SOMEID} can be set to a true value to cause a
# given sequence to be skipped over.

sub __next_hunk_id
{
	my ($diffset, %ignore) = @_;
	my ($lo_id, $lo_start);
	foreach my $id (keys %$diffset)
	{
		next if $ignore{$id};
		my $diff = $diffset->{$id};
		next if $#$diff < 0;
		my $start = $diff->[0]->{start};
		if ((! defined($lo_start))
		    || $start < $lo_start)
		{
			$lo_id = $id;
			$lo_start = $start;
		}
	}
	return $lo_id;
}


# Converts all the hunks in an Algorithm::Diff-style diff to a
# normalised form in which all hunks are a) still internally
# contiguous, and b) have start indices which refer to items in the
# original array, before any diffs are applied. Normally, hunks
# consisting of only inserts don't meet criterion b).

sub __homogenise_diff
{
	my @hdiff = ();
	my $delta = 0;   # difference between orig and resultant
	foreach my $orig_hunk (@_)
	{
		my ($first_op, $start) = @{$orig_hunk->[0]} [0, 1];
		$start -= $delta  if $first_op eq '+';
		my $hhunk = {
			start => $start,
			changes => [],
		};
		foreach my $change (@$orig_hunk)
		{
			my ($op, $data);
			($op, undef, $data) = @$change;
			$delta += (($op eq '+') ? 1 : -1);
			push @{$hhunk->{changes}}, [$op, $data];
		}
		push @hdiff, $hhunk;
	}
	return @hdiff;
}


1;
