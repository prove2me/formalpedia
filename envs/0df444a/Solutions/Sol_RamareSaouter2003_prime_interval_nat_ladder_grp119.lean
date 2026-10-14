-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp119
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T19:35:00.038467+00:00
-- url     : https://prove2.me/submissions/aa8de348-d1d9-4cad-880d-e4941ba8fd7e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05901
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05902
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05903
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05904
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05905
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05906
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05907
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05908
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05909
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05910
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05911
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05912
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05913
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05914
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05915
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05916
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05917
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05918
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05919
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05920
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05921
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05922
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05923
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05924
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05925
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05926
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05927
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05928
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05929
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05930
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05931
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05932
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05933
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05934
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05935
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05936
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05937
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05938
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05939
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05940
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05941
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05942
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05943
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05944
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05945
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05946
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05947
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05948
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05949
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05950

theorem solution (n : Nat)
    (hn : 39629926580993773 < n) (hupper : n <= 45647159062049219) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 42532249398506473 n with h2 | h2
  · -- n > 42532249398506473
    rcases Nat.lt_or_ge 43999954133471227 n with h4 | h4
    · -- n > 43999954133471227
      rcases Nat.lt_or_ge 44752693416525599 n with h6 | h6
      · -- n > 44752693416525599
        rcases Nat.lt_or_ge 45133866286588867 n with h8 | h8
        · -- n > 45133866286588867
          rcases Nat.lt_or_ge 45389789419889077 n with h10 | h10
          · -- n > 45389789419889077
            rcases Nat.lt_or_ge 45518296254706841 n with h12 | h12
            · -- n > 45518296254706841
              exact RamareSaouter2003.prime_interval_nat_ladder_c05950 n (by omega) (by omega)
            · -- n <= 45518296254706841
              exact RamareSaouter2003.prime_interval_nat_ladder_c05949 n (by omega) (by omega)
          · -- n <= 45389789419889077
            rcases Nat.lt_or_ge 45261644241289841 n with h12 | h12
            · -- n > 45261644241289841
              exact RamareSaouter2003.prime_interval_nat_ladder_c05948 n (by omega) (by omega)
            · -- n <= 45261644241289841
              exact RamareSaouter2003.prime_interval_nat_ladder_c05947 n (by omega) (by omega)
        · -- n <= 45133866286588867
          rcases Nat.lt_or_ge 44879392484933549 n with h10 | h10
          · -- n > 44879392484933549
            rcases Nat.lt_or_ge 45006442096294619 n with h12 | h12
            · -- n > 45006442096294619
              exact RamareSaouter2003.prime_interval_nat_ladder_c05946 n (by omega) (by omega)
            · -- n <= 45006442096294619
              exact RamareSaouter2003.prime_interval_nat_ladder_c05945 n (by omega) (by omega)
          · -- n <= 44879392484933549
            exact RamareSaouter2003.prime_interval_nat_ladder_c05944 n (by omega) (by omega)
      · -- n <= 44752693416525599
        rcases Nat.lt_or_ge 44374723559512391 n with h8 | h8
        · -- n > 44374723559512391
          rcases Nat.lt_or_ge 44500356104466253 n with h10 | h10
          · -- n > 44500356104466253
            rcases Nat.lt_or_ge 44626348758324649 n with h12 | h12
            · -- n > 44626348758324649
              exact RamareSaouter2003.prime_interval_nat_ladder_c05943 n (by omega) (by omega)
            · -- n <= 44626348758324649
              exact RamareSaouter2003.prime_interval_nat_ladder_c05942 n (by omega) (by omega)
          · -- n <= 44500356104466253
            exact RamareSaouter2003.prime_interval_nat_ladder_c05941 n (by omega) (by omega)
        · -- n <= 44374723559512391
          rcases Nat.lt_or_ge 44124523531080407 n with h10 | h10
          · -- n > 44124523531080407
            rcases Nat.lt_or_ge 44249440657272041 n with h12 | h12
            · -- n > 44249440657272041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05940 n (by omega) (by omega)
            · -- n <= 44249440657272041
              exact RamareSaouter2003.prime_interval_nat_ladder_c05939 n (by omega) (by omega)
          · -- n <= 44124523531080407
            exact RamareSaouter2003.prime_interval_nat_ladder_c05938 n (by omega) (by omega)
    · -- n <= 43999954133471227
      rcases Nat.lt_or_ge 43259880251026937 n with h6 | h6
      · -- n > 43259880251026937
        rcases Nat.lt_or_ge 43628336339888851 n with h8 | h8
        · -- n > 43628336339888851
          rcases Nat.lt_or_ge 43751854360265549 n with h10 | h10
          · -- n > 43751854360265549
            rcases Nat.lt_or_ge 43875728802459767 n with h12 | h12
            · -- n > 43875728802459767
              exact RamareSaouter2003.prime_interval_nat_ladder_c05937 n (by omega) (by omega)
            · -- n <= 43875728802459767
              exact RamareSaouter2003.prime_interval_nat_ladder_c05936 n (by omega) (by omega)
          · -- n <= 43751854360265549
            exact RamareSaouter2003.prime_interval_nat_ladder_c05935 n (by omega) (by omega)
        · -- n <= 43628336339888851
          rcases Nat.lt_or_ge 43382352298888717 n with h10 | h10
          · -- n > 43382352298888717
            rcases Nat.lt_or_ge 43505178153505331 n with h12 | h12
            · -- n > 43505178153505331
              exact RamareSaouter2003.prime_interval_nat_ladder_c05934 n (by omega) (by omega)
            · -- n <= 43505178153505331
              exact RamareSaouter2003.prime_interval_nat_ladder_c05933 n (by omega) (by omega)
          · -- n <= 43382352298888717
            exact RamareSaouter2003.prime_interval_nat_ladder_c05932 n (by omega) (by omega)
      · -- n <= 43259880251026937
        rcases Nat.lt_or_ge 42894517970346137 n with h8 | h8
        · -- n > 42894517970346137
          rcases Nat.lt_or_ge 43015959440146577 n with h10 | h10
          · -- n > 43015959440146577
            rcases Nat.lt_or_ge 43137747445324927 n with h12 | h12
            · -- n > 43137747445324927
              exact RamareSaouter2003.prime_interval_nat_ladder_c05931 n (by omega) (by omega)
            · -- n <= 43137747445324927
              exact RamareSaouter2003.prime_interval_nat_ladder_c05930 n (by omega) (by omega)
          · -- n <= 43015959440146577
            exact RamareSaouter2003.prime_interval_nat_ladder_c05929 n (by omega) (by omega)
        · -- n <= 42894517970346137
          rcases Nat.lt_or_ge 42652659347550433 n with h10 | h10
          · -- n > 42652659347550433
            rcases Nat.lt_or_ge 42773418189767519 n with h12 | h12
            · -- n > 42773418189767519
              exact RamareSaouter2003.prime_interval_nat_ladder_c05928 n (by omega) (by omega)
            · -- n <= 42773418189767519
              exact RamareSaouter2003.prime_interval_nat_ladder_c05927 n (by omega) (by omega)
          · -- n <= 42652659347550433
            exact RamareSaouter2003.prime_interval_nat_ladder_c05926 n (by omega) (by omega)
  · -- n <= 42532249398506473
    rcases Nat.lt_or_ge 40997431269123001 n with h4 | h4
    · -- n > 40997431269123001
      rcases Nat.lt_or_ge 41698812515294401 n with h6 | h6
      · -- n > 41698812515294401
        rcases Nat.lt_or_ge 42053960777744219 n with h8 | h8
        · -- n > 42053960777744219
          rcases Nat.lt_or_ge 42292427912770331 n with h10 | h10
          · -- n > 42292427912770331
            rcases Nat.lt_or_ge 42412170701904799 n with h12 | h12
            · -- n > 42412170701904799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05925 n (by omega) (by omega)
            · -- n <= 42412170701904799
              exact RamareSaouter2003.prime_interval_nat_ladder_c05924 n (by omega) (by omega)
          · -- n <= 42292427912770331
            rcases Nat.lt_or_ge 42173026487355103 n with h12 | h12
            · -- n > 42173026487355103
              exact RamareSaouter2003.prime_interval_nat_ladder_c05923 n (by omega) (by omega)
            · -- n <= 42173026487355103
              exact RamareSaouter2003.prime_interval_nat_ladder_c05922 n (by omega) (by omega)
        · -- n <= 42053960777744219
          rcases Nat.lt_or_ge 41816848367986451 n with h10 | h10
          · -- n > 41816848367986451
            rcases Nat.lt_or_ge 41935239492774601 n with h12 | h12
            · -- n > 41935239492774601
              exact RamareSaouter2003.prime_interval_nat_ladder_c05921 n (by omega) (by omega)
            · -- n <= 41935239492774601
              exact RamareSaouter2003.prime_interval_nat_ladder_c05920 n (by omega) (by omega)
          · -- n <= 41816848367986451
            exact RamareSaouter2003.prime_interval_nat_ladder_c05919 n (by omega) (by omega)
      · -- n <= 41698812515294401
        rcases Nat.lt_or_ge 41346643632576467 n with h8 | h8
        · -- n > 41346643632576467
          rcases Nat.lt_or_ge 41463700617244601 n with h10 | h10
          · -- n > 41463700617244601
            rcases Nat.lt_or_ge 41581084558773059 n with h12 | h12
            · -- n > 41581084558773059
              exact RamareSaouter2003.prime_interval_nat_ladder_c05918 n (by omega) (by omega)
            · -- n <= 41581084558773059
              exact RamareSaouter2003.prime_interval_nat_ladder_c05917 n (by omega) (by omega)
          · -- n <= 41463700617244601
            exact RamareSaouter2003.prime_interval_nat_ladder_c05916 n (by omega) (by omega)
        · -- n <= 41346643632576467
          rcases Nat.lt_or_ge 41113507009271479 n with h10 | h10
          · -- n > 41113507009271479
            rcases Nat.lt_or_ge 41229911704916639 n with h12 | h12
            · -- n > 41229911704916639
              exact RamareSaouter2003.prime_interval_nat_ladder_c05915 n (by omega) (by omega)
            · -- n <= 41229911704916639
              exact RamareSaouter2003.prime_interval_nat_ladder_c05914 n (by omega) (by omega)
          · -- n <= 41113507009271479
            exact RamareSaouter2003.prime_interval_nat_ladder_c05913 n (by omega) (by omega)
    · -- n <= 40997431269123001
      rcases Nat.lt_or_ge 40307864671258577 n with h6 | h6
      · -- n > 40307864671258577
        rcases Nat.lt_or_ge 40651190268026941 n with h8 | h8
        · -- n > 40651190268026941
          rcases Nat.lt_or_ge 40766265130828609 n with h10 | h10
          · -- n > 40766265130828609
            rcases Nat.lt_or_ge 40881682998214087 n with h12 | h12
            · -- n > 40881682998214087
              exact RamareSaouter2003.prime_interval_nat_ladder_c05912 n (by omega) (by omega)
            · -- n <= 40881682998214087
              exact RamareSaouter2003.prime_interval_nat_ladder_c05911 n (by omega) (by omega)
          · -- n <= 40766265130828609
            exact RamareSaouter2003.prime_interval_nat_ladder_c05910 n (by omega) (by omega)
        · -- n <= 40651190268026941
          rcases Nat.lt_or_ge 40421987678246693 n with h10 | h10
          · -- n > 40421987678246693
            rcases Nat.lt_or_ge 40536422607854609 n with h12 | h12
            · -- n > 40536422607854609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05909 n (by omega) (by omega)
            · -- n <= 40536422607854609
              exact RamareSaouter2003.prime_interval_nat_ladder_c05908 n (by omega) (by omega)
          · -- n <= 40421987678246693
            exact RamareSaouter2003.prime_interval_nat_ladder_c05907 n (by omega) (by omega)
      · -- n <= 40307864671258577
        rcases Nat.lt_or_ge 39967473223968013 n with h8 | h8
        · -- n > 39967473223968013
          rcases Nat.lt_or_ge 40080599138294581 n with h10 | h10
          · -- n > 40080599138294581
            rcases Nat.lt_or_ge 40194066994132309 n with h12 | h12
            · -- n > 40194066994132309
              exact RamareSaouter2003.prime_interval_nat_ladder_c05906 n (by omega) (by omega)
            · -- n <= 40194066994132309
              exact RamareSaouter2003.prime_interval_nat_ladder_c05905 n (by omega) (by omega)
          · -- n <= 40080599138294581
            exact RamareSaouter2003.prime_interval_nat_ladder_c05904 n (by omega) (by omega)
        · -- n <= 39967473223968013
          rcases Nat.lt_or_ge 39742124405266837 n with h10 | h10
          · -- n > 39742124405266837
            rcases Nat.lt_or_ge 39854638118600089 n with h12 | h12
            · -- n > 39854638118600089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05903 n (by omega) (by omega)
            · -- n <= 39854638118600089
              exact RamareSaouter2003.prime_interval_nat_ladder_c05902 n (by omega) (by omega)
          · -- n <= 39742124405266837
            exact RamareSaouter2003.prime_interval_nat_ladder_c05901 n (by omega) (by omega)
