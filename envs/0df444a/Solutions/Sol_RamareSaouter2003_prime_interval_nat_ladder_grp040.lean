-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp040
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T13:58:27.550913+00:00
-- url     : https://prove2.me/submissions/b5730b73-e63b-49ca-b421-f8e29b0f94a3

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01951
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01952
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01953
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01954
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01955
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01956
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01957
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01958
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01959
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01960
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01961
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01962
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01963
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01964
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01965
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01966
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01967
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01968
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01969
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01970
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01971
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01972
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01973
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01974
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01975
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01976
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01977
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01978
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01979
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01980
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01981
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01982
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01983
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01984
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01985
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01986
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01987
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01988
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01989
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01990
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01991
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01992
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01993
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01994
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01995
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01996
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01997
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01998
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01999
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02000

theorem solution (n : Nat)
    (hn : 1104932290381 < n) (hupper : n <= 1254452690677) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1177334164483 n with h2 | h2
  · -- n > 1177334164483
    rcases Nat.lt_or_ge 1213744057891 n with h4 | h4
    · -- n > 1213744057891
      rcases Nat.lt_or_ge 1232366764963 n with h6 | h6
      · -- n > 1232366764963
        rcases Nat.lt_or_ge 1241784406459 n with h8 | h8
        · -- n > 1241784406459
          rcases Nat.lt_or_ge 1248102563287 n with h10 | h10
          · -- n > 1248102563287
            rcases Nat.lt_or_ge 1251273620647 n with h12 | h12
            · -- n > 1251273620647
              exact RamareSaouter2003.prime_interval_nat_ladder_c02000 n (by omega) (by omega)
            · -- n <= 1251273620647
              exact RamareSaouter2003.prime_interval_nat_ladder_c01999 n (by omega) (by omega)
          · -- n <= 1248102563287
            rcases Nat.lt_or_ge 1244939498731 n with h12 | h12
            · -- n > 1244939498731
              exact RamareSaouter2003.prime_interval_nat_ladder_c01998 n (by omega) (by omega)
            · -- n <= 1244939498731
              exact RamareSaouter2003.prime_interval_nat_ladder_c01997 n (by omega) (by omega)
        · -- n <= 1241784406459
          rcases Nat.lt_or_ge 1235498059417 n with h10 | h10
          · -- n > 1235498059417
            rcases Nat.lt_or_ge 1238637266641 n with h12 | h12
            · -- n > 1238637266641
              exact RamareSaouter2003.prime_interval_nat_ladder_c01996 n (by omega) (by omega)
            · -- n <= 1238637266641
              exact RamareSaouter2003.prime_interval_nat_ladder_c01995 n (by omega) (by omega)
          · -- n <= 1235498059417
            exact RamareSaouter2003.prime_interval_nat_ladder_c01994 n (by omega) (by omega)
      · -- n <= 1232366764963
        rcases Nat.lt_or_ge 1223020159663 n with h8 | h8
        · -- n > 1223020159663
          rcases Nat.lt_or_ge 1226127834839 n with h10 | h10
          · -- n > 1226127834839
            rcases Nat.lt_or_ge 1229243363353 n with h12 | h12
            · -- n > 1229243363353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01993 n (by omega) (by omega)
            · -- n <= 1229243363353
              exact RamareSaouter2003.prime_interval_nat_ladder_c01992 n (by omega) (by omega)
          · -- n <= 1226127834839
            exact RamareSaouter2003.prime_interval_nat_ladder_c01991 n (by omega) (by omega)
        · -- n <= 1223020159663
          rcases Nat.lt_or_ge 1216828290863 n with h10 | h10
          · -- n > 1216828290863
            rcases Nat.lt_or_ge 1219920318271 n with h12 | h12
            · -- n > 1219920318271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01990 n (by omega) (by omega)
            · -- n <= 1219920318271
              exact RamareSaouter2003.prime_interval_nat_ladder_c01989 n (by omega) (by omega)
          · -- n <= 1216828290863
            exact RamareSaouter2003.prime_interval_nat_ladder_c01988 n (by omega) (by omega)
    · -- n <= 1213744057891
      rcases Nat.lt_or_ge 1195401252319 n with h6 | h6
      · -- n > 1195401252319
        rcases Nat.lt_or_ge 1204537930417 n with h8 | h8
        · -- n > 1204537930417
          rcases Nat.lt_or_ge 1207598897159 n with h10 | h10
          · -- n > 1207598897159
            rcases Nat.lt_or_ge 1210667599879 n with h12 | h12
            · -- n > 1210667599879
              exact RamareSaouter2003.prime_interval_nat_ladder_c01987 n (by omega) (by omega)
            · -- n <= 1210667599879
              exact RamareSaouter2003.prime_interval_nat_ladder_c01986 n (by omega) (by omega)
          · -- n <= 1207598897159
            exact RamareSaouter2003.prime_interval_nat_ladder_c01985 n (by omega) (by omega)
        · -- n <= 1204537930417
          rcases Nat.lt_or_ge 1198439127341 n with h10 | h10
          · -- n > 1198439127341
            rcases Nat.lt_or_ge 1201484680247 n with h12 | h12
            · -- n > 1201484680247
              exact RamareSaouter2003.prime_interval_nat_ladder_c01984 n (by omega) (by omega)
            · -- n <= 1201484680247
              exact RamareSaouter2003.prime_interval_nat_ladder_c01983 n (by omega) (by omega)
          · -- n <= 1198439127341
            exact RamareSaouter2003.prime_interval_nat_ladder_c01982 n (by omega) (by omega)
      · -- n <= 1195401252319
        rcases Nat.lt_or_ge 1186333502899 n with h8 | h8
        · -- n > 1186333502899
          rcases Nat.lt_or_ge 1189348459319 n with h10 | h10
          · -- n > 1189348459319
            rcases Nat.lt_or_ge 1192371036037 n with h12 | h12
            · -- n > 1192371036037
              exact RamareSaouter2003.prime_interval_nat_ladder_c01981 n (by omega) (by omega)
            · -- n <= 1192371036037
              exact RamareSaouter2003.prime_interval_nat_ladder_c01980 n (by omega) (by omega)
          · -- n <= 1189348459319
            exact RamareSaouter2003.prime_interval_nat_ladder_c01979 n (by omega) (by omega)
        · -- n <= 1186333502899
          rcases Nat.lt_or_ge 1180326374449 n with h10 | h10
          · -- n > 1180326374449
            rcases Nat.lt_or_ge 1183326147613 n with h12 | h12
            · -- n > 1183326147613
              exact RamareSaouter2003.prime_interval_nat_ladder_c01978 n (by omega) (by omega)
            · -- n <= 1183326147613
              exact RamareSaouter2003.prime_interval_nat_ladder_c01977 n (by omega) (by omega)
          · -- n <= 1180326374449
            exact RamareSaouter2003.prime_interval_nat_ladder_c01976 n (by omega) (by omega)
  · -- n <= 1177334164483
    rcases Nat.lt_or_ge 1139115117031 n with h4 | h4
    · -- n > 1139115117031
      rcases Nat.lt_or_ge 1156598875903 n with h6 | h6
      · -- n > 1156598875903
        rcases Nat.lt_or_ge 1165440577549 n with h8 | h8
        · -- n > 1165440577549
          rcases Nat.lt_or_ge 1171372358129 n with h10 | h10
          · -- n > 1171372358129
            rcases Nat.lt_or_ge 1174349498681 n with h12 | h12
            · -- n > 1174349498681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01975 n (by omega) (by omega)
            · -- n <= 1174349498681
              exact RamareSaouter2003.prime_interval_nat_ladder_c01974 n (by omega) (by omega)
          · -- n <= 1171372358129
            rcases Nat.lt_or_ge 1168402723993 n with h12 | h12
            · -- n > 1168402723993
              exact RamareSaouter2003.prime_interval_nat_ladder_c01973 n (by omega) (by omega)
            · -- n <= 1168402723993
              exact RamareSaouter2003.prime_interval_nat_ladder_c01972 n (by omega) (by omega)
        · -- n <= 1165440577549
          rcases Nat.lt_or_ge 1159538672143 n with h10 | h10
          · -- n > 1159538672143
            rcases Nat.lt_or_ge 1162485899851 n with h12 | h12
            · -- n > 1162485899851
              exact RamareSaouter2003.prime_interval_nat_ladder_c01971 n (by omega) (by omega)
            · -- n <= 1162485899851
              exact RamareSaouter2003.prime_interval_nat_ladder_c01970 n (by omega) (by omega)
          · -- n <= 1159538672143
            exact RamareSaouter2003.prime_interval_nat_ladder_c01969 n (by omega) (by omega)
      · -- n <= 1156598875903
        rcases Nat.lt_or_ge 1147823889281 n with h8 | h8
        · -- n > 1147823889281
          rcases Nat.lt_or_ge 1150741502987 n with h10 | h10
          · -- n > 1150741502987
            rcases Nat.lt_or_ge 1153666492369 n with h12 | h12
            · -- n > 1153666492369
              exact RamareSaouter2003.prime_interval_nat_ladder_c01968 n (by omega) (by omega)
            · -- n <= 1153666492369
              exact RamareSaouter2003.prime_interval_nat_ladder_c01967 n (by omega) (by omega)
          · -- n <= 1150741502987
            exact RamareSaouter2003.prime_interval_nat_ladder_c01966 n (by omega) (by omega)
        · -- n <= 1147823889281
          rcases Nat.lt_or_ge 1142010714697 n with h10 | h10
          · -- n > 1142010714697
            rcases Nat.lt_or_ge 1144913632649 n with h12 | h12
            · -- n > 1144913632649
              exact RamareSaouter2003.prime_interval_nat_ladder_c01965 n (by omega) (by omega)
            · -- n <= 1144913632649
              exact RamareSaouter2003.prime_interval_nat_ladder_c01964 n (by omega) (by omega)
          · -- n <= 1142010714697
            exact RamareSaouter2003.prime_interval_nat_ladder_c01963 n (by omega) (by omega)
    · -- n <= 1139115117031
      rcases Nat.lt_or_ge 1121894232157 n with h6 | h6
      · -- n > 1121894232157
        rcases Nat.lt_or_ge 1130472062393 n with h8 | h8
        · -- n > 1130472062393
          rcases Nat.lt_or_ge 1133345809153 n with h10 | h10
          · -- n > 1133345809153
            rcases Nat.lt_or_ge 1136226821287 n with h12 | h12
            · -- n > 1136226821287
              exact RamareSaouter2003.prime_interval_nat_ladder_c01962 n (by omega) (by omega)
            · -- n <= 1136226821287
              exact RamareSaouter2003.prime_interval_nat_ladder_c01961 n (by omega) (by omega)
          · -- n <= 1133345809153
            exact RamareSaouter2003.prime_interval_nat_ladder_c01960 n (by omega) (by omega)
        · -- n <= 1130472062393
          rcases Nat.lt_or_ge 1124746292027 n with h10 | h10
          · -- n > 1124746292027
            rcases Nat.lt_or_ge 1127605562771 n with h12 | h12
            · -- n > 1127605562771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01959 n (by omega) (by omega)
            · -- n <= 1127605562771
              exact RamareSaouter2003.prime_interval_nat_ladder_c01958 n (by omega) (by omega)
          · -- n <= 1124746292027
            exact RamareSaouter2003.prime_interval_nat_ladder_c01957 n (by omega) (by omega)
      · -- n <= 1121894232157
        rcases Nat.lt_or_ge 1113381136817 n with h8 | h8
        · -- n > 1113381136817
          rcases Nat.lt_or_ge 1116211672447 n with h10 | h10
          · -- n > 1116211672447
            rcases Nat.lt_or_ge 1119049364959 n with h12 | h12
            · -- n > 1119049364959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01956 n (by omega) (by omega)
            · -- n <= 1119049364959
              exact RamareSaouter2003.prime_interval_nat_ladder_c01955 n (by omega) (by omega)
          · -- n <= 1116211672447
            exact RamareSaouter2003.prime_interval_nat_ladder_c01954 n (by omega) (by omega)
        · -- n <= 1113381136817
          rcases Nat.lt_or_ge 1107741463579 n with h10 | h10
          · -- n > 1107741463579
            rcases Nat.lt_or_ge 1110557739787 n with h12 | h12
            · -- n > 1110557739787
              exact RamareSaouter2003.prime_interval_nat_ladder_c01953 n (by omega) (by omega)
            · -- n <= 1110557739787
              exact RamareSaouter2003.prime_interval_nat_ladder_c01952 n (by omega) (by omega)
          · -- n <= 1107741463579
            exact RamareSaouter2003.prime_interval_nat_ladder_c01951 n (by omega) (by omega)
