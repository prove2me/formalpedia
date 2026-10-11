-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T23:20:10.498982+00:00
-- url     : https://prove2.me/submissions/421ff222-6c63-4336-bd68-2204884e347f

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00751
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00752
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00753
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00754
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00755
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00756
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00757
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00758
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00759
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00760
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00761
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00762
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00763
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00764
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00765
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00766
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00767
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00768
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00769
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00770
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00771
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00772
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00773
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00774
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00775
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00776
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00777
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00778
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00779
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00780
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00781
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00782
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00783
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00784
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00785
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00786
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00787
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00788
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00789
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00790
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00791
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00792
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00793
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00794
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00795
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00796
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00797
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00798
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00799
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00800

theorem solution (n : Nat)
    (hn : 56954749447 < n) (hupper : n <= 63861919811) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 60307306781 n with h2 | h2
  · -- n > 60307306781
    rcases Nat.lt_or_ge 61987555493 n with h4 | h4
    · -- n > 61987555493
      rcases Nat.lt_or_ge 62845555211 n with h6 | h6
      · -- n > 62845555211
        rcases Nat.lt_or_ge 63279099343 n with h8 | h8
        · -- n > 63279099343
          rcases Nat.lt_or_ge 63569826613 n with h10 | h10
          · -- n > 63569826613
            rcases Nat.lt_or_ge 63715702073 n with h12 | h12
            · -- n > 63715702073
              exact RamareSaouter2003.prime_interval_nat_ladder_c00800 n (by omega) (by omega)
            · -- n <= 63715702073
              exact RamareSaouter2003.prime_interval_nat_ladder_c00799 n (by omega) (by omega)
          · -- n <= 63569826613
            rcases Nat.lt_or_ge 63424292629 n with h12 | h12
            · -- n > 63424292629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00798 n (by omega) (by omega)
            · -- n <= 63424292629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00797 n (by omega) (by omega)
        · -- n <= 63279099343
          rcases Nat.lt_or_ge 62989731443 n with h10 | h10
          · -- n > 62989731443
            rcases Nat.lt_or_ge 63134245891 n with h12 | h12
            · -- n > 63134245891
              exact RamareSaouter2003.prime_interval_nat_ladder_c00796 n (by omega) (by omega)
            · -- n <= 63134245891
              exact RamareSaouter2003.prime_interval_nat_ladder_c00795 n (by omega) (by omega)
          · -- n <= 62989731443
            exact RamareSaouter2003.prime_interval_nat_ladder_c00794 n (by omega) (by omega)
      · -- n <= 62845555211
        rcases Nat.lt_or_ge 62415047969 n with h8 | h8
        · -- n > 62415047969
          rcases Nat.lt_or_ge 62558214353 n with h10 | h10
          · -- n > 62558214353
            rcases Nat.lt_or_ge 62701716397 n with h12 | h12
            · -- n > 62701716397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00793 n (by omega) (by omega)
            · -- n <= 62701716397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00792 n (by omega) (by omega)
          · -- n <= 62558214353
            exact RamareSaouter2003.prime_interval_nat_ladder_c00791 n (by omega) (by omega)
        · -- n <= 62415047969
          rcases Nat.lt_or_ge 62129719321 n with h10 | h10
          · -- n > 62129719321
            rcases Nat.lt_or_ge 62272216547 n with h12 | h12
            · -- n > 62272216547
              exact RamareSaouter2003.prime_interval_nat_ladder_c00790 n (by omega) (by omega)
            · -- n <= 62272216547
              exact RamareSaouter2003.prime_interval_nat_ladder_c00789 n (by omega) (by omega)
          · -- n <= 62129719321
            exact RamareSaouter2003.prime_interval_nat_ladder_c00788 n (by omega) (by omega)
    · -- n <= 61987555493
      rcases Nat.lt_or_ge 61141529539 n with h6 | h6
      · -- n > 61141529539
        rcases Nat.lt_or_ge 61563056497 n with h8 | h8
        · -- n > 61563056497
          rcases Nat.lt_or_ge 61704224851 n with h10 | h10
          · -- n > 61704224851
            rcases Nat.lt_or_ge 61845724267 n with h12 | h12
            · -- n > 61845724267
              exact RamareSaouter2003.prime_interval_nat_ladder_c00787 n (by omega) (by omega)
            · -- n <= 61845724267
              exact RamareSaouter2003.prime_interval_nat_ladder_c00786 n (by omega) (by omega)
          · -- n <= 61704224851
            exact RamareSaouter2003.prime_interval_nat_ladder_c00785 n (by omega) (by omega)
        · -- n <= 61563056497
          rcases Nat.lt_or_ge 61281709631 n with h10 | h10
          · -- n > 61281709631
            rcases Nat.lt_or_ge 61422218321 n with h12 | h12
            · -- n > 61422218321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00784 n (by omega) (by omega)
            · -- n <= 61422218321
              exact RamareSaouter2003.prime_interval_nat_ladder_c00783 n (by omega) (by omega)
          · -- n <= 61281709631
            exact RamareSaouter2003.prime_interval_nat_ladder_c00782 n (by omega) (by omega)
      · -- n <= 61141529539
        rcases Nat.lt_or_ge 60722953321 n with h8 | h8
        · -- n > 60722953321
          rcases Nat.lt_or_ge 60862152179 n with h10 | h10
          · -- n > 60862152179
            rcases Nat.lt_or_ge 61001677309 n with h12 | h12
            · -- n > 61001677309
              exact RamareSaouter2003.prime_interval_nat_ladder_c00781 n (by omega) (by omega)
            · -- n <= 61001677309
              exact RamareSaouter2003.prime_interval_nat_ladder_c00780 n (by omega) (by omega)
          · -- n <= 60862152179
            exact RamareSaouter2003.prime_interval_nat_ladder_c00779 n (by omega) (by omega)
        · -- n <= 60722953321
          rcases Nat.lt_or_ge 60445531387 n with h10 | h10
          · -- n > 60445531387
            rcases Nat.lt_or_ge 60584079977 n with h12 | h12
            · -- n > 60584079977
              exact RamareSaouter2003.prime_interval_nat_ladder_c00778 n (by omega) (by omega)
            · -- n <= 60584079977
              exact RamareSaouter2003.prime_interval_nat_ladder_c00777 n (by omega) (by omega)
          · -- n <= 60445531387
            exact RamareSaouter2003.prime_interval_nat_ladder_c00776 n (by omega) (by omega)
  · -- n <= 60307306781
    rcases Nat.lt_or_ge 58539518113 n with h4 | h4
    · -- n > 58539518113
      rcases Nat.lt_or_ge 59348740859 n with h6 | h6
      · -- n > 59348740859
        rcases Nat.lt_or_ge 59757632657 n with h8 | h8
        · -- n > 59757632657
          rcases Nat.lt_or_ge 60031826401 n with h10 | h10
          · -- n > 60031826401
            rcases Nat.lt_or_ge 60169405343 n with h12 | h12
            · -- n > 60169405343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00775 n (by omega) (by omega)
            · -- n <= 60169405343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00774 n (by omega) (by omega)
          · -- n <= 60031826401
            rcases Nat.lt_or_ge 59894569057 n with h12 | h12
            · -- n > 59894569057
              exact RamareSaouter2003.prime_interval_nat_ladder_c00773 n (by omega) (by omega)
            · -- n <= 59894569057
              exact RamareSaouter2003.prime_interval_nat_ladder_c00772 n (by omega) (by omega)
        · -- n <= 59757632657
          rcases Nat.lt_or_ge 59484719269 n with h10 | h10
          · -- n > 59484719269
            rcases Nat.lt_or_ge 59621016283 n with h12 | h12
            · -- n > 59621016283
              exact RamareSaouter2003.prime_interval_nat_ladder_c00771 n (by omega) (by omega)
            · -- n <= 59621016283
              exact RamareSaouter2003.prime_interval_nat_ladder_c00770 n (by omega) (by omega)
          · -- n <= 59484719269
            exact RamareSaouter2003.prime_interval_nat_ladder_c00769 n (by omega) (by omega)
      · -- n <= 59348740859
        rcases Nat.lt_or_ge 58942709479 n with h8 | h8
        · -- n > 58942709479
          rcases Nat.lt_or_ge 59077736723 n with h10 | h10
          · -- n > 59077736723
            rcases Nat.lt_or_ge 59213080279 n with h12 | h12
            · -- n > 59213080279
              exact RamareSaouter2003.prime_interval_nat_ladder_c00768 n (by omega) (by omega)
            · -- n <= 59213080279
              exact RamareSaouter2003.prime_interval_nat_ladder_c00767 n (by omega) (by omega)
          · -- n <= 59077736723
            exact RamareSaouter2003.prime_interval_nat_ladder_c00766 n (by omega) (by omega)
        · -- n <= 58942709479
          rcases Nat.lt_or_ge 58673600957 n with h10 | h10
          · -- n > 58673600957
            rcases Nat.lt_or_ge 58807997783 n with h12 | h12
            · -- n > 58807997783
              exact RamareSaouter2003.prime_interval_nat_ladder_c00765 n (by omega) (by omega)
            · -- n <= 58807997783
              exact RamareSaouter2003.prime_interval_nat_ladder_c00764 n (by omega) (by omega)
          · -- n <= 58673600957
            exact RamareSaouter2003.prime_interval_nat_ladder_c00763 n (by omega) (by omega)
    · -- n <= 58539518113
      rcases Nat.lt_or_ge 57741574487 n with h6 | h6
      · -- n > 57741574487
        rcases Nat.lt_or_ge 58139146529 n with h8 | h8
        · -- n > 58139146529
          rcases Nat.lt_or_ge 58272291647 n with h10 | h10
          · -- n > 58272291647
            rcases Nat.lt_or_ge 58405748633 n with h12 | h12
            · -- n > 58405748633
              exact RamareSaouter2003.prime_interval_nat_ladder_c00762 n (by omega) (by omega)
            · -- n <= 58405748633
              exact RamareSaouter2003.prime_interval_nat_ladder_c00761 n (by omega) (by omega)
          · -- n <= 58272291647
            exact RamareSaouter2003.prime_interval_nat_ladder_c00760 n (by omega) (by omega)
        · -- n <= 58139146529
          rcases Nat.lt_or_ge 57873788683 n with h10 | h10
          · -- n > 57873788683
            rcases Nat.lt_or_ge 58006312453 n with h12 | h12
            · -- n > 58006312453
              exact RamareSaouter2003.prime_interval_nat_ladder_c00759 n (by omega) (by omega)
            · -- n <= 58006312453
              exact RamareSaouter2003.prime_interval_nat_ladder_c00758 n (by omega) (by omega)
          · -- n <= 57873788683
            exact RamareSaouter2003.prime_interval_nat_ladder_c00757 n (by omega) (by omega)
      · -- n <= 57741574487
        rcases Nat.lt_or_ge 57346782013 n with h8 | h8
        · -- n > 57346782013
          rcases Nat.lt_or_ge 57478071883 n with h10 | h10
          · -- n > 57478071883
            rcases Nat.lt_or_ge 57609669137 n with h12 | h12
            · -- n > 57609669137
              exact RamareSaouter2003.prime_interval_nat_ladder_c00756 n (by omega) (by omega)
            · -- n <= 57609669137
              exact RamareSaouter2003.prime_interval_nat_ladder_c00755 n (by omega) (by omega)
          · -- n <= 57478071883
            exact RamareSaouter2003.prime_interval_nat_ladder_c00754 n (by omega) (by omega)
        · -- n <= 57346782013
          rcases Nat.lt_or_ge 57085121521 n with h10 | h10
          · -- n > 57085121521
            rcases Nat.lt_or_ge 57215798851 n with h12 | h12
            · -- n > 57215798851
              exact RamareSaouter2003.prime_interval_nat_ladder_c00753 n (by omega) (by omega)
            · -- n <= 57215798851
              exact RamareSaouter2003.prime_interval_nat_ladder_c00752 n (by omega) (by omega)
          · -- n <= 57085121521
            exact RamareSaouter2003.prime_interval_nat_ladder_c00751 n (by omega) (by omega)
