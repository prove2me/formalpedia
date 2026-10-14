-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp079
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T08:07:14.478602+00:00
-- url     : https://prove2.me/submissions/7f04c4be-2748-431a-bb28-c0662758b973

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03950

theorem solution (n : Nat)
    (hn : 140346528528637 < n) (hupper : n <= 160082286934001) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 149292794017519 n with h2 | h2
  · -- n > 149292794017519
    rcases Nat.lt_or_ge 154315249920389 n with h4 | h4
    · -- n > 154315249920389
      rcases Nat.lt_or_ge 156948702271541 n with h6 | h6
      · -- n > 156948702271541
        rcases Nat.lt_or_ge 158283445391993 n with h8 | h8
        · -- n > 158283445391993
          rcases Nat.lt_or_ge 159179905299071 n with h10 | h10
          · -- n > 159179905299071
            rcases Nat.lt_or_ge 159630411144641 n with h12 | h12
            · -- n > 159630411144641
              exact RamareSaouter2003.prime_interval_nat_ladder_c03950 n (by omega) (by omega)
            · -- n <= 159630411144641
              exact RamareSaouter2003.prime_interval_nat_ladder_c03949 n (by omega) (by omega)
          · -- n <= 159179905299071
            rcases Nat.lt_or_ge 158731094813999 n with h12 | h12
            · -- n > 158731094813999
              exact RamareSaouter2003.prime_interval_nat_ladder_c03948 n (by omega) (by omega)
            · -- n <= 158731094813999
              exact RamareSaouter2003.prime_interval_nat_ladder_c03947 n (by omega) (by omega)
        · -- n <= 158283445391993
          rcases Nat.lt_or_ge 157392152498479 n with h10 | h10
          · -- n > 157392152498479
            rcases Nat.lt_or_ge 157837308998903 n with h12 | h12
            · -- n > 157837308998903
              exact RamareSaouter2003.prime_interval_nat_ladder_c03946 n (by omega) (by omega)
            · -- n <= 157837308998903
              exact RamareSaouter2003.prime_interval_nat_ladder_c03945 n (by omega) (by omega)
          · -- n <= 157392152498479
            exact RamareSaouter2003.prime_interval_nat_ladder_c03944 n (by omega) (by omega)
      · -- n <= 156948702271541
        rcases Nat.lt_or_ge 155625473242649 n with h8 | h8
        · -- n > 155625473242649
          rcases Nat.lt_or_ge 156065302933627 n with h10 | h10
          · -- n > 156065302933627
            rcases Nat.lt_or_ge 156506302691969 n with h12 | h12
            · -- n > 156506302691969
              exact RamareSaouter2003.prime_interval_nat_ladder_c03943 n (by omega) (by omega)
            · -- n <= 156506302691969
              exact RamareSaouter2003.prime_interval_nat_ladder_c03942 n (by omega) (by omega)
          · -- n <= 156065302933627
            exact RamareSaouter2003.prime_interval_nat_ladder_c03941 n (by omega) (by omega)
        · -- n <= 155625473242649
          rcases Nat.lt_or_ge 154750811665949 n with h10 | h10
          · -- n > 154750811665949
            rcases Nat.lt_or_ge 155187709885067 n with h12 | h12
            · -- n > 155187709885067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03940 n (by omega) (by omega)
            · -- n <= 155187709885067
              exact RamareSaouter2003.prime_interval_nat_ladder_c03939 n (by omega) (by omega)
          · -- n <= 154750811665949
            exact RamareSaouter2003.prime_interval_nat_ladder_c03938 n (by omega) (by omega)
    · -- n <= 154315249920389
      rcases Nat.lt_or_ge 151730929985827 n with h6 | h6
      · -- n > 151730929985827
        rcases Nat.lt_or_ge 153017591148691 n with h8 | h8
        · -- n > 153017591148691
          rcases Nat.lt_or_ge 153448048400681 n with h10 | h10
          · -- n > 153448048400681
            rcases Nat.lt_or_ge 153880798099921 n with h12 | h12
            · -- n > 153880798099921
              exact RamareSaouter2003.prime_interval_nat_ladder_c03937 n (by omega) (by omega)
            · -- n <= 153880798099921
              exact RamareSaouter2003.prime_interval_nat_ladder_c03936 n (by omega) (by omega)
          · -- n <= 153448048400681
            exact RamareSaouter2003.prime_interval_nat_ladder_c03935 n (by omega) (by omega)
        · -- n <= 153017591148691
          rcases Nat.lt_or_ge 152158662695867 n with h10 | h10
          · -- n > 152158662695867
            rcases Nat.lt_or_ge 152587713643303 n with h12 | h12
            · -- n > 152587713643303
              exact RamareSaouter2003.prime_interval_nat_ladder_c03934 n (by omega) (by omega)
            · -- n <= 152587713643303
              exact RamareSaouter2003.prime_interval_nat_ladder_c03933 n (by omega) (by omega)
          · -- n <= 152158662695867
            exact RamareSaouter2003.prime_interval_nat_ladder_c03932 n (by omega) (by omega)
      · -- n <= 151730929985827
        rcases Nat.lt_or_ge 150455563560979 n with h8 | h8
        · -- n > 150455563560979
          rcases Nat.lt_or_ge 150879383940347 n with h10 | h10
          · -- n > 150879383940347
            rcases Nat.lt_or_ge 151304488474829 n with h12 | h12
            · -- n > 151304488474829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03931 n (by omega) (by omega)
            · -- n <= 151304488474829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03930 n (by omega) (by omega)
          · -- n <= 150879383940347
            exact RamareSaouter2003.prime_interval_nat_ladder_c03929 n (by omega) (by omega)
        · -- n <= 150455563560979
          rcases Nat.lt_or_ge 149662562660561 n with h10 | h10
          · -- n > 149662562660561
            rcases Nat.lt_or_ge 150033271988491 n with h12 | h12
            · -- n > 150033271988491
              exact RamareSaouter2003.prime_interval_nat_ladder_c03928 n (by omega) (by omega)
            · -- n <= 150033271988491
              exact RamareSaouter2003.prime_interval_nat_ladder_c03927 n (by omega) (by omega)
          · -- n <= 149662562660561
            exact RamareSaouter2003.prime_interval_nat_ladder_c03926 n (by omega) (by omega)
  · -- n <= 149292794017519
    rcases Nat.lt_or_ge 144571575434417 n with h4 | h4
    · -- n > 144571575434417
      rcases Nat.lt_or_ge 146731559408717 n with h6 | h6
      · -- n > 146731559408717
        rcases Nat.lt_or_ge 147823623213533 n with h8 | h8
        · -- n > 147823623213533
          rcases Nat.lt_or_ge 148556239402037 n with h10 | h10
          · -- n > 148556239402037
            rcases Nat.lt_or_ge 148924020557971 n with h12 | h12
            · -- n > 148924020557971
              exact RamareSaouter2003.prime_interval_nat_ladder_c03925 n (by omega) (by omega)
            · -- n <= 148924020557971
              exact RamareSaouter2003.prime_interval_nat_ladder_c03924 n (by omega) (by omega)
          · -- n <= 148556239402037
            rcases Nat.lt_or_ge 148189447678781 n with h12 | h12
            · -- n > 148189447678781
              exact RamareSaouter2003.prime_interval_nat_ladder_c03923 n (by omega) (by omega)
            · -- n <= 148189447678781
              exact RamareSaouter2003.prime_interval_nat_ladder_c03922 n (by omega) (by omega)
        · -- n <= 147823623213533
          rcases Nat.lt_or_ge 147094681304803 n with h10 | h10
          · -- n > 147094681304803
            rcases Nat.lt_or_ge 147458701831783 n with h12 | h12
            · -- n > 147458701831783
              exact RamareSaouter2003.prime_interval_nat_ladder_c03921 n (by omega) (by omega)
            · -- n <= 147458701831783
              exact RamareSaouter2003.prime_interval_nat_ladder_c03920 n (by omega) (by omega)
          · -- n <= 147094681304803
            exact RamareSaouter2003.prime_interval_nat_ladder_c03919 n (by omega) (by omega)
      · -- n <= 146731559408717
        rcases Nat.lt_or_ge 145647563349781 n with h8 | h8
        · -- n > 145647563349781
          rcases Nat.lt_or_ge 146008002641621 n with h10 | h10
          · -- n > 146008002641621
            rcases Nat.lt_or_ge 146369333925253 n with h12 | h12
            · -- n > 146369333925253
              exact RamareSaouter2003.prime_interval_nat_ladder_c03918 n (by omega) (by omega)
            · -- n <= 146369333925253
              exact RamareSaouter2003.prime_interval_nat_ladder_c03917 n (by omega) (by omega)
          · -- n <= 146008002641621
            exact RamareSaouter2003.prime_interval_nat_ladder_c03916 n (by omega) (by omega)
        · -- n <= 145647563349781
          rcases Nat.lt_or_ge 144929351940017 n with h10 | h10
          · -- n > 144929351940017
            rcases Nat.lt_or_ge 145288013848093 n with h12 | h12
            · -- n > 145288013848093
              exact RamareSaouter2003.prime_interval_nat_ladder_c03915 n (by omega) (by omega)
            · -- n <= 145288013848093
              exact RamareSaouter2003.prime_interval_nat_ladder_c03914 n (by omega) (by omega)
          · -- n <= 144929351940017
            exact RamareSaouter2003.prime_interval_nat_ladder_c03913 n (by omega) (by omega)
    · -- n <= 144571575434417
      rcases Nat.lt_or_ge 142443387828799 n with h6 | h6
      · -- n > 142443387828799
        rcases Nat.lt_or_ge 143503536502061 n with h8 | h8
        · -- n > 143503536502061
          rcases Nat.lt_or_ge 143858669893153 n with h10 | h10
          · -- n > 143858669893153
            rcases Nat.lt_or_ge 144214682145503 n with h12 | h12
            · -- n > 144214682145503
              exact RamareSaouter2003.prime_interval_nat_ladder_c03912 n (by omega) (by omega)
            · -- n <= 144214682145503
              exact RamareSaouter2003.prime_interval_nat_ladder_c03911 n (by omega) (by omega)
          · -- n <= 143858669893153
            exact RamareSaouter2003.prime_interval_nat_ladder_c03910 n (by omega) (by omega)
        · -- n <= 143503536502061
          rcases Nat.lt_or_ge 142795897631561 n with h10 | h10
          · -- n > 142795897631561
            rcases Nat.lt_or_ge 143149279802917 n with h12 | h12
            · -- n > 143149279802917
              exact RamareSaouter2003.prime_interval_nat_ladder_c03909 n (by omega) (by omega)
            · -- n <= 143149279802917
              exact RamareSaouter2003.prime_interval_nat_ladder_c03908 n (by omega) (by omega)
          · -- n <= 142795897631561
            exact RamareSaouter2003.prime_interval_nat_ladder_c03907 n (by omega) (by omega)
      · -- n <= 142443387828799
        rcases Nat.lt_or_ge 141391071124151 n with h8 | h8
        · -- n > 141391071124151
          rcases Nat.lt_or_ge 141740976720731 n with h10 | h10
          · -- n > 141740976720731
            rcases Nat.lt_or_ge 142091748241241 n with h12 | h12
            · -- n > 142091748241241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03906 n (by omega) (by omega)
            · -- n <= 142091748241241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03905 n (by omega) (by omega)
          · -- n <= 141740976720731
            exact RamareSaouter2003.prime_interval_nat_ladder_c03904 n (by omega) (by omega)
        · -- n <= 141391071124151
          rcases Nat.lt_or_ge 140693849157907 n with h10 | h10
          · -- n > 140693849157907
            rcases Nat.lt_or_ge 141042029314099 n with h12 | h12
            · -- n > 141042029314099
              exact RamareSaouter2003.prime_interval_nat_ladder_c03903 n (by omega) (by omega)
            · -- n <= 141042029314099
              exact RamareSaouter2003.prime_interval_nat_ladder_c03902 n (by omega) (by omega)
          · -- n <= 140693849157907
            exact RamareSaouter2003.prime_interval_nat_ladder_c03901 n (by omega) (by omega)
