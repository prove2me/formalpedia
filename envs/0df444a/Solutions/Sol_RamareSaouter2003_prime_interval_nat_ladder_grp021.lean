-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp021
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T02:30:31.511187+00:00
-- url     : https://prove2.me/submissions/a3d6bd91-8f31-49ab-a00d-7ba3732bb1ec

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01050

theorem solution (n : Nat)
    (hn : 101332544893 < n) (hupper : n <= 114760011811) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 107835538049 n with h2 | h2
  · -- n > 107835538049
    rcases Nat.lt_or_ge 111105027617 n with h4 | h4
    · -- n > 111105027617
      rcases Nat.lt_or_ge 112777112527 n with h6 | h6
      · -- n > 112777112527
        rcases Nat.lt_or_ge 113622656767 n with h8 | h8
        · -- n > 113622656767
          rcases Nat.lt_or_ge 114189905051 n with h10 | h10
          · -- n > 114189905051
            rcases Nat.lt_or_ge 114474600193 n with h12 | h12
            · -- n > 114474600193
              exact RamareSaouter2003.prime_interval_nat_ladder_c01050 n (by omega) (by omega)
            · -- n <= 114474600193
              exact RamareSaouter2003.prime_interval_nat_ladder_c01049 n (by omega) (by omega)
          · -- n <= 114189905051
            rcases Nat.lt_or_ge 113905924507 n with h12 | h12
            · -- n > 113905924507
              exact RamareSaouter2003.prime_interval_nat_ladder_c01048 n (by omega) (by omega)
            · -- n <= 113905924507
              exact RamareSaouter2003.prime_interval_nat_ladder_c01047 n (by omega) (by omega)
        · -- n <= 113622656767
          rcases Nat.lt_or_ge 113058252611 n with h10 | h10
          · -- n > 113058252611
            rcases Nat.lt_or_ge 113340100141 n with h12 | h12
            · -- n > 113340100141
              exact RamareSaouter2003.prime_interval_nat_ladder_c01046 n (by omega) (by omega)
            · -- n <= 113340100141
              exact RamareSaouter2003.prime_interval_nat_ladder_c01045 n (by omega) (by omega)
          · -- n <= 113058252611
            exact RamareSaouter2003.prime_interval_nat_ladder_c01044 n (by omega) (by omega)
      · -- n <= 112777112527
        rcases Nat.lt_or_ge 111937918849 n with h8 | h8
        · -- n > 111937918849
          rcases Nat.lt_or_ge 112216947443 n with h10 | h10
          · -- n > 112216947443
            rcases Nat.lt_or_ge 112496678089 n with h12 | h12
            · -- n > 112496678089
              exact RamareSaouter2003.prime_interval_nat_ladder_c01043 n (by omega) (by omega)
            · -- n <= 112496678089
              exact RamareSaouter2003.prime_interval_nat_ladder_c01042 n (by omega) (by omega)
          · -- n <= 112216947443
            exact RamareSaouter2003.prime_interval_nat_ladder_c01041 n (by omega) (by omega)
        · -- n <= 111937918849
          rcases Nat.lt_or_ge 111381960733 n with h10 | h10
          · -- n > 111381960733
            rcases Nat.lt_or_ge 111659590529 n with h12 | h12
            · -- n > 111659590529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01040 n (by omega) (by omega)
            · -- n <= 111659590529
              exact RamareSaouter2003.prime_interval_nat_ladder_c01039 n (by omega) (by omega)
          · -- n <= 111381960733
            exact RamareSaouter2003.prime_interval_nat_ladder_c01038 n (by omega) (by omega)
    · -- n <= 111105027617
      rcases Nat.lt_or_ge 109457962139 n with h6 | h6
      · -- n > 109457962139
        rcases Nat.lt_or_ge 110278391191 n with h8 | h8
        · -- n > 110278391191
          rcases Nat.lt_or_ge 110553244661 n with h10 | h10
          · -- n > 110553244661
            rcases Nat.lt_or_ge 110828789507 n with h12 | h12
            · -- n > 110828789507
              exact RamareSaouter2003.prime_interval_nat_ladder_c01037 n (by omega) (by omega)
            · -- n <= 110828789507
              exact RamareSaouter2003.prime_interval_nat_ladder_c01036 n (by omega) (by omega)
          · -- n <= 110553244661
            exact RamareSaouter2003.prime_interval_nat_ladder_c01035 n (by omega) (by omega)
        · -- n <= 110278391191
          rcases Nat.lt_or_ge 109730751679 n with h10 | h10
          · -- n > 109730751679
            rcases Nat.lt_or_ge 110004227461 n with h12 | h12
            · -- n > 110004227461
              exact RamareSaouter2003.prime_interval_nat_ladder_c01034 n (by omega) (by omega)
            · -- n <= 110004227461
              exact RamareSaouter2003.prime_interval_nat_ladder_c01033 n (by omega) (by omega)
          · -- n <= 109730751679
            exact RamareSaouter2003.prime_interval_nat_ladder_c01032 n (by omega) (by omega)
      · -- n <= 109457962139
        rcases Nat.lt_or_ge 108643693259 n with h8 | h8
        · -- n > 108643693259
          rcases Nat.lt_or_ge 108914434619 n with h10 | h10
          · -- n > 108914434619
            rcases Nat.lt_or_ge 109185856991 n with h12 | h12
            · -- n > 109185856991
              exact RamareSaouter2003.prime_interval_nat_ladder_c01031 n (by omega) (by omega)
            · -- n <= 109185856991
              exact RamareSaouter2003.prime_interval_nat_ladder_c01030 n (by omega) (by omega)
          · -- n <= 108914434619
            exact RamareSaouter2003.prime_interval_nat_ladder_c01029 n (by omega) (by omega)
        · -- n <= 108643693259
          rcases Nat.lt_or_ge 108104246713 n with h10 | h10
          · -- n > 108104246713
            rcases Nat.lt_or_ge 108373631237 n with h12 | h12
            · -- n > 108373631237
              exact RamareSaouter2003.prime_interval_nat_ladder_c01028 n (by omega) (by omega)
            · -- n <= 108373631237
              exact RamareSaouter2003.prime_interval_nat_ladder_c01027 n (by omega) (by omega)
          · -- n <= 108104246713
            exact RamareSaouter2003.prime_interval_nat_ladder_c01026 n (by omega) (by omega)
  · -- n <= 107835538049
    rcases Nat.lt_or_ge 104403055457 n with h4 | h4
    · -- n > 104403055457
      rcases Nat.lt_or_ge 105973358207 n with h6 | h6
      · -- n > 105973358207
        rcases Nat.lt_or_ge 106767427787 n with h8 | h8
        · -- n > 106767427787
          rcases Nat.lt_or_ge 107300141471 n with h10 | h10
          · -- n > 107300141471
            rcases Nat.lt_or_ge 107567503513 n with h12 | h12
            · -- n > 107567503513
              exact RamareSaouter2003.prime_interval_nat_ladder_c01025 n (by omega) (by omega)
            · -- n <= 107567503513
              exact RamareSaouter2003.prime_interval_nat_ladder_c01024 n (by omega) (by omega)
          · -- n <= 107300141471
            rcases Nat.lt_or_ge 107033450123 n with h12 | h12
            · -- n > 107033450123
              exact RamareSaouter2003.prime_interval_nat_ladder_c01023 n (by omega) (by omega)
            · -- n <= 107033450123
              exact RamareSaouter2003.prime_interval_nat_ladder_c01022 n (by omega) (by omega)
        · -- n <= 106767427787
          rcases Nat.lt_or_ge 106237383533 n with h10 | h10
          · -- n > 106237383533
            rcases Nat.lt_or_ge 106502072839 n with h12 | h12
            · -- n > 106502072839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01021 n (by omega) (by omega)
            · -- n <= 106502072839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01020 n (by omega) (by omega)
          · -- n <= 106237383533
            exact RamareSaouter2003.prime_interval_nat_ladder_c01019 n (by omega) (by omega)
      · -- n <= 105973358207
        rcases Nat.lt_or_ge 105185249111 n with h8 | h8
        · -- n > 105185249111
          rcases Nat.lt_or_ge 105447292637 n with h10 | h10
          · -- n > 105447292637
            rcases Nat.lt_or_ge 105709995113 n with h12 | h12
            · -- n > 105709995113
              exact RamareSaouter2003.prime_interval_nat_ladder_c01018 n (by omega) (by omega)
            · -- n <= 105709995113
              exact RamareSaouter2003.prime_interval_nat_ladder_c01017 n (by omega) (by omega)
          · -- n <= 105447292637
            exact RamareSaouter2003.prime_interval_nat_ladder_c01016 n (by omega) (by omega)
        · -- n <= 105185249111
          rcases Nat.lt_or_ge 104663132173 n with h10 | h10
          · -- n > 104663132173
            rcases Nat.lt_or_ge 104923862839 n with h12 | h12
            · -- n > 104923862839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01015 n (by omega) (by omega)
            · -- n <= 104923862839
              exact RamareSaouter2003.prime_interval_nat_ladder_c01014 n (by omega) (by omega)
          · -- n <= 104663132173
            exact RamareSaouter2003.prime_interval_nat_ladder_c01013 n (by omega) (by omega)
    · -- n <= 104403055457
      rcases Nat.lt_or_ge 102856235917 n with h6 | h6
      · -- n > 102856235917
        rcases Nat.lt_or_ge 103626732593 n with h8 | h8
        · -- n > 103626732593
          rcases Nat.lt_or_ge 103884857393 n with h10 | h10
          · -- n > 103884857393
            rcases Nat.lt_or_ge 104143631107 n with h12 | h12
            · -- n > 104143631107
              exact RamareSaouter2003.prime_interval_nat_ladder_c01012 n (by omega) (by omega)
            · -- n <= 104143631107
              exact RamareSaouter2003.prime_interval_nat_ladder_c01011 n (by omega) (by omega)
          · -- n <= 103884857393
            exact RamareSaouter2003.prime_interval_nat_ladder_c01010 n (by omega) (by omega)
        · -- n <= 103626732593
          rcases Nat.lt_or_ge 103112423551 n with h10 | h10
          · -- n > 103112423551
            rcases Nat.lt_or_ge 103369255177 n with h12 | h12
            · -- n > 103369255177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01009 n (by omega) (by omega)
            · -- n <= 103369255177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01008 n (by omega) (by omega)
          · -- n <= 103112423551
            exact RamareSaouter2003.prime_interval_nat_ladder_c01007 n (by omega) (by omega)
      · -- n <= 102856235917
        rcases Nat.lt_or_ge 102091521313 n with h8 | h8
        · -- n > 102091521313
          rcases Nat.lt_or_ge 102345786373 n with h10 | h10
          · -- n > 102345786373
            rcases Nat.lt_or_ge 102600690701 n with h12 | h12
            · -- n > 102600690701
              exact RamareSaouter2003.prime_interval_nat_ladder_c01006 n (by omega) (by omega)
            · -- n <= 102600690701
              exact RamareSaouter2003.prime_interval_nat_ladder_c01005 n (by omega) (by omega)
          · -- n <= 102345786373
            exact RamareSaouter2003.prime_interval_nat_ladder_c01004 n (by omega) (by omega)
        · -- n <= 102091521313
          rcases Nat.lt_or_ge 101584902173 n with h10 | h10
          · -- n > 101584902173
            rcases Nat.lt_or_ge 101837893771 n with h12 | h12
            · -- n > 101837893771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01003 n (by omega) (by omega)
            · -- n <= 101837893771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01002 n (by omega) (by omega)
          · -- n <= 101584902173
            exact RamareSaouter2003.prime_interval_nat_ladder_c01001 n (by omega) (by omega)
