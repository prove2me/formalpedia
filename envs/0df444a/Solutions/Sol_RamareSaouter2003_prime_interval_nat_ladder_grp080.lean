-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp080
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T08:24:38.059705+00:00
-- url     : https://prove2.me/submissions/9b7112fa-385c-4433-b13d-f223482810db

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04000

theorem solution (n : Nat)
    (hn : 160082286934001 < n) (hupper : n <= 184372641394199) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 171800233345969 n with h2 | h2
  · -- n > 171800233345969
    rcases Nat.lt_or_ge 177725234695829 n with h4 | h4
    · -- n > 177725234695829
      rcases Nat.lt_or_ge 180763232794511 n with h6 | h6
      · -- n > 180763232794511
        rcases Nat.lt_or_ge 182300568848521 n with h8 | h8
        · -- n > 182300568848521
          rcases Nat.lt_or_ge 183333869222839 n with h10 | h10
          · -- n > 183333869222839
            rcases Nat.lt_or_ge 183852332706727 n with h12 | h12
            · -- n > 183852332706727
              exact RamareSaouter2003.prime_interval_nat_ladder_c04000 n (by omega) (by omega)
            · -- n <= 183852332706727
              exact RamareSaouter2003.prime_interval_nat_ladder_c03999 n (by omega) (by omega)
          · -- n <= 183333869222839
            rcases Nat.lt_or_ge 182816489254453 n with h12 | h12
            · -- n > 182816489254453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03998 n (by omega) (by omega)
            · -- n <= 182816489254453
              exact RamareSaouter2003.prime_interval_nat_ladder_c03997 n (by omega) (by omega)
        · -- n <= 182300568848521
          rcases Nat.lt_or_ge 181273527530327 n with h10 | h10
          · -- n > 181273527530327
            rcases Nat.lt_or_ge 181786024869643 n with h12 | h12
            · -- n > 181786024869643
              exact RamareSaouter2003.prime_interval_nat_ladder_c03996 n (by omega) (by omega)
            · -- n <= 181786024869643
              exact RamareSaouter2003.prime_interval_nat_ladder_c03995 n (by omega) (by omega)
          · -- n <= 181273527530327
            exact RamareSaouter2003.prime_interval_nat_ladder_c03994 n (by omega) (by omega)
      · -- n <= 180763232794511
        rcases Nat.lt_or_ge 179238217646659 n with h8 | h8
        · -- n > 179238217646659
          rcases Nat.lt_or_ge 179744640455449 n with h10 | h10
          · -- n > 179744640455449
            rcases Nat.lt_or_ge 180253147831811 n with h12 | h12
            · -- n > 180253147831811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03993 n (by omega) (by omega)
            · -- n <= 180253147831811
              exact RamareSaouter2003.prime_interval_nat_ladder_c03992 n (by omega) (by omega)
          · -- n <= 179744640455449
            exact RamareSaouter2003.prime_interval_nat_ladder_c03991 n (by omega) (by omega)
        · -- n <= 179238217646659
          rcases Nat.lt_or_ge 178227888474023 n with h10 | h10
          · -- n > 178227888474023
            rcases Nat.lt_or_ge 178732482370513 n with h12 | h12
            · -- n > 178732482370513
              exact RamareSaouter2003.prime_interval_nat_ladder_c03990 n (by omega) (by omega)
            · -- n <= 178732482370513
              exact RamareSaouter2003.prime_interval_nat_ladder_c03989 n (by omega) (by omega)
          · -- n <= 178227888474023
            exact RamareSaouter2003.prime_interval_nat_ladder_c03988 n (by omega) (by omega)
    · -- n <= 177725234695829
      rcases Nat.lt_or_ge 174737699588789 n with h6 | h6
      · -- n > 174737699588789
        rcases Nat.lt_or_ge 176225407595323 n with h8 | h8
        · -- n > 176225407595323
          rcases Nat.lt_or_ge 176724289209971 n with h10 | h10
          · -- n > 176724289209971
            rcases Nat.lt_or_ge 177223636497653 n with h12 | h12
            · -- n > 177223636497653
              exact RamareSaouter2003.prime_interval_nat_ladder_c03987 n (by omega) (by omega)
            · -- n <= 177223636497653
              exact RamareSaouter2003.prime_interval_nat_ladder_c03986 n (by omega) (by omega)
          · -- n <= 176724289209971
            exact RamareSaouter2003.prime_interval_nat_ladder_c03985 n (by omega) (by omega)
        · -- n <= 176225407595323
          rcases Nat.lt_or_ge 175232381601971 n with h10 | h10
          · -- n > 175232381601971
            rcases Nat.lt_or_ge 175728133222511 n with h12 | h12
            · -- n > 175728133222511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03984 n (by omega) (by omega)
            · -- n <= 175728133222511
              exact RamareSaouter2003.prime_interval_nat_ladder_c03983 n (by omega) (by omega)
          · -- n <= 175232381601971
            exact RamareSaouter2003.prime_interval_nat_ladder_c03982 n (by omega) (by omega)
      · -- n <= 174737699588789
        rcases Nat.lt_or_ge 173263038189037 n with h8 | h8
        · -- n > 173263038189037
          rcases Nat.lt_or_ge 173753545977877 n with h10 | h10
          · -- n > 173753545977877
            rcases Nat.lt_or_ge 174245011340993 n with h12 | h12
            · -- n > 174245011340993
              exact RamareSaouter2003.prime_interval_nat_ladder_c03981 n (by omega) (by omega)
            · -- n <= 174245011340993
              exact RamareSaouter2003.prime_interval_nat_ladder_c03980 n (by omega) (by omega)
          · -- n <= 173753545977877
            exact RamareSaouter2003.prime_interval_nat_ladder_c03979 n (by omega) (by omega)
        · -- n <= 173263038189037
          rcases Nat.lt_or_ge 172286621885347 n with h10 | h10
          · -- n > 172286621885347
            rcases Nat.lt_or_ge 172773959024837 n with h12 | h12
            · -- n > 172773959024837
              exact RamareSaouter2003.prime_interval_nat_ladder_c03978 n (by omega) (by omega)
            · -- n <= 172773959024837
              exact RamareSaouter2003.prime_interval_nat_ladder_c03977 n (by omega) (by omega)
          · -- n <= 172286621885347
            exact RamareSaouter2003.prime_interval_nat_ladder_c03976 n (by omega) (by omega)
  · -- n <= 171800233345969
    rcases Nat.lt_or_ge 165603127411639 n with h4 | h4
    · -- n > 165603127411639
      rcases Nat.lt_or_ge 168434450624093 n with h6 | h6
      · -- n > 168434450624093
        rcases Nat.lt_or_ge 169868417221871 n with h8 | h8
        · -- n > 169868417221871
          rcases Nat.lt_or_ge 170831561751743 n with h10 | h10
          · -- n > 170831561751743
            rcases Nat.lt_or_ge 171315189362231 n with h12 | h12
            · -- n > 171315189362231
              exact RamareSaouter2003.prime_interval_nat_ladder_c03975 n (by omega) (by omega)
            · -- n <= 171315189362231
              exact RamareSaouter2003.prime_interval_nat_ladder_c03974 n (by omega) (by omega)
          · -- n <= 170831561751743
            rcases Nat.lt_or_ge 170349296918249 n with h12 | h12
            · -- n > 170349296918249
              exact RamareSaouter2003.prime_interval_nat_ladder_c03973 n (by omega) (by omega)
            · -- n <= 170349296918249
              exact RamareSaouter2003.prime_interval_nat_ladder_c03972 n (by omega) (by omega)
        · -- n <= 169868417221871
          rcases Nat.lt_or_ge 168911192337281 n with h10 | h10
          · -- n > 168911192337281
            rcases Nat.lt_or_ge 169389127838279 n with h12 | h12
            · -- n > 169389127838279
              exact RamareSaouter2003.prime_interval_nat_ladder_c03971 n (by omega) (by omega)
            · -- n <= 169389127838279
              exact RamareSaouter2003.prime_interval_nat_ladder_c03970 n (by omega) (by omega)
          · -- n <= 168911192337281
            exact RamareSaouter2003.prime_interval_nat_ladder_c03969 n (by omega) (by omega)
      · -- n <= 168434450624093
        rcases Nat.lt_or_ge 167012506897793 n with h8 | h8
        · -- n > 167012506897793
          rcases Nat.lt_or_ge 167485317947611 n with h10 | h10
          · -- n > 167485317947611
            rcases Nat.lt_or_ge 167959004490071 n with h12 | h12
            · -- n > 167959004490071
              exact RamareSaouter2003.prime_interval_nat_ladder_c03968 n (by omega) (by omega)
            · -- n <= 167959004490071
              exact RamareSaouter2003.prime_interval_nat_ladder_c03967 n (by omega) (by omega)
          · -- n <= 167485317947611
            exact RamareSaouter2003.prime_interval_nat_ladder_c03966 n (by omega) (by omega)
        · -- n <= 167012506897793
          rcases Nat.lt_or_ge 166071518375669 n with h10 | h10
          · -- n > 166071518375669
            rcases Nat.lt_or_ge 166541034240829 n with h12 | h12
            · -- n > 166541034240829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03965 n (by omega) (by omega)
            · -- n <= 166541034240829
              exact RamareSaouter2003.prime_interval_nat_ladder_c03964 n (by omega) (by omega)
          · -- n <= 166071518375669
            exact RamareSaouter2003.prime_interval_nat_ladder_c03963 n (by omega) (by omega)
    · -- n <= 165603127411639
      rcases Nat.lt_or_ge 162820072198123 n with h6 | h6
      · -- n > 162820072198123
        rcases Nat.lt_or_ge 164206076719837 n with h8 | h8
        · -- n > 164206076719837
          rcases Nat.lt_or_ge 164670794458151 n with h10 | h10
          · -- n > 164670794458151
            rcases Nat.lt_or_ge 165135912240133 n with h12 | h12
            · -- n > 165135912240133
              exact RamareSaouter2003.prime_interval_nat_ladder_c03962 n (by omega) (by omega)
            · -- n <= 165135912240133
              exact RamareSaouter2003.prime_interval_nat_ladder_c03961 n (by omega) (by omega)
          · -- n <= 164670794458151
            exact RamareSaouter2003.prime_interval_nat_ladder_c03960 n (by omega) (by omega)
        · -- n <= 164206076719837
          rcases Nat.lt_or_ge 163280501196277 n with h10 | h10
          · -- n > 163280501196277
            rcases Nat.lt_or_ge 163742603772103 n with h12 | h12
            · -- n > 163742603772103
              exact RamareSaouter2003.prime_interval_nat_ladder_c03959 n (by omega) (by omega)
            · -- n <= 163742603772103
              exact RamareSaouter2003.prime_interval_nat_ladder_c03958 n (by omega) (by omega)
          · -- n <= 163280501196277
            exact RamareSaouter2003.prime_interval_nat_ladder_c03957 n (by omega) (by omega)
      · -- n <= 162820072198123
        rcases Nat.lt_or_ge 161445635603017 n with h8 | h8
        · -- n > 161445635603017
          rcases Nat.lt_or_ge 161902718258761 n with h10 | h10
          · -- n > 161902718258761
            rcases Nat.lt_or_ge 162360727483853 n with h12 | h12
            · -- n > 162360727483853
              exact RamareSaouter2003.prime_interval_nat_ladder_c03956 n (by omega) (by omega)
            · -- n <= 162360727483853
              exact RamareSaouter2003.prime_interval_nat_ladder_c03955 n (by omega) (by omega)
          · -- n <= 161902718258761
            exact RamareSaouter2003.prime_interval_nat_ladder_c03954 n (by omega) (by omega)
        · -- n <= 161445635603017
          rcases Nat.lt_or_ge 160535384850937 n with h10 | h10
          · -- n > 160535384850937
            rcases Nat.lt_or_ge 160989909333703 n with h12 | h12
            · -- n > 160989909333703
              exact RamareSaouter2003.prime_interval_nat_ladder_c03953 n (by omega) (by omega)
            · -- n <= 160989909333703
              exact RamareSaouter2003.prime_interval_nat_ladder_c03952 n (by omega) (by omega)
          · -- n <= 160535384850937
            exact RamareSaouter2003.prime_interval_nat_ladder_c03951 n (by omega) (by omega)
