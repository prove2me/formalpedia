-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp062
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T02:13:14.964868+00:00
-- url     : https://prove2.me/submissions/157ff357-996a-40f3-8ae4-ba7a2dd0214b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03100

theorem solution (n : Nat)
    (hn : 17170407053213 < n) (hupper : n <= 19429088181631) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 18264866623151 n with h2 | h2
  · -- n > 18264866623151
    rcases Nat.lt_or_ge 18814719325967 n with h4 | h4
    · -- n > 18814719325967
      rcases Nat.lt_or_ge 19095822247399 n with h6 | h6
      · -- n > 19095822247399
        rcases Nat.lt_or_ge 19237944748991 n with h8 | h8
        · -- n > 19237944748991
          rcases Nat.lt_or_ge 19333280243297 n with h10 | h10
          · -- n > 19333280243297
            rcases Nat.lt_or_ge 19381125010777 n with h12 | h12
            · -- n > 19381125010777
              exact RamareSaouter2003.prime_interval_nat_ladder_c03100 n (by omega) (by omega)
            · -- n <= 19381125010777
              exact RamareSaouter2003.prime_interval_nat_ladder_c03099 n (by omega) (by omega)
          · -- n <= 19333280243297
            rcases Nat.lt_or_ge 19285553586461 n with h12 | h12
            · -- n > 19285553586461
              exact RamareSaouter2003.prime_interval_nat_ladder_c03098 n (by omega) (by omega)
            · -- n <= 19285553586461
              exact RamareSaouter2003.prime_interval_nat_ladder_c03097 n (by omega) (by omega)
        · -- n <= 19237944748991
          rcases Nat.lt_or_ge 19143079369237 n with h10 | h10
          · -- n > 19143079369237
            rcases Nat.lt_or_ge 19190453439977 n with h12 | h12
            · -- n > 19190453439977
              exact RamareSaouter2003.prime_interval_nat_ladder_c03096 n (by omega) (by omega)
            · -- n <= 19190453439977
              exact RamareSaouter2003.prime_interval_nat_ladder_c03095 n (by omega) (by omega)
          · -- n <= 19143079369237
            exact RamareSaouter2003.prime_interval_nat_ladder_c03094 n (by omega) (by omega)
      · -- n <= 19095822247399
        rcases Nat.lt_or_ge 18954749691961 n with h8 | h8
        · -- n > 18954749691961
          rcases Nat.lt_or_ge 19001657696389 n with h10 | h10
          · -- n > 19001657696389
            rcases Nat.lt_or_ge 19048681785799 n with h12 | h12
            · -- n > 19048681785799
              exact RamareSaouter2003.prime_interval_nat_ladder_c03093 n (by omega) (by omega)
            · -- n <= 19048681785799
              exact RamareSaouter2003.prime_interval_nat_ladder_c03092 n (by omega) (by omega)
          · -- n <= 19001657696389
            exact RamareSaouter2003.prime_interval_nat_ladder_c03091 n (by omega) (by omega)
        · -- n <= 18954749691961
          rcases Nat.lt_or_ge 18861280792213 n with h10 | h10
          · -- n > 18861280792213
            rcases Nat.lt_or_ge 18907957485841 n with h12 | h12
            · -- n > 18907957485841
              exact RamareSaouter2003.prime_interval_nat_ladder_c03090 n (by omega) (by omega)
            · -- n <= 18907957485841
              exact RamareSaouter2003.prime_interval_nat_ladder_c03089 n (by omega) (by omega)
          · -- n <= 18861280792213
            exact RamareSaouter2003.prime_interval_nat_ladder_c03088 n (by omega) (by omega)
    · -- n <= 18814719325967
      rcases Nat.lt_or_ge 18537754422853 n with h6 | h6
      · -- n > 18537754422853
        rcases Nat.lt_or_ge 18675723450541 n with h8 | h8
        · -- n > 18675723450541
          rcases Nat.lt_or_ge 18721940938559 n with h10 | h10
          · -- n > 18721940938559
            rcases Nat.lt_or_ge 18768272802667 n with h12 | h12
            · -- n > 18768272802667
              exact RamareSaouter2003.prime_interval_nat_ladder_c03087 n (by omega) (by omega)
            · -- n <= 18768272802667
              exact RamareSaouter2003.prime_interval_nat_ladder_c03086 n (by omega) (by omega)
          · -- n <= 18721940938559
            exact RamareSaouter2003.prime_interval_nat_ladder_c03085 n (by omega) (by omega)
        · -- n <= 18675723450541
          rcases Nat.lt_or_ge 18583630473911 n with h10 | h10
          · -- n > 18583630473911
            rcases Nat.lt_or_ge 18629620056227 n with h12 | h12
            · -- n > 18629620056227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03084 n (by omega) (by omega)
            · -- n <= 18629620056227
              exact RamareSaouter2003.prime_interval_nat_ladder_c03083 n (by omega) (by omega)
          · -- n <= 18583630473911
            exact RamareSaouter2003.prime_interval_nat_ladder_c03082 n (by omega) (by omega)
      · -- n <= 18537754422853
        rcases Nat.lt_or_ge 18400804657163 n with h8 | h8
        · -- n > 18400804657163
          rcases Nat.lt_or_ge 18446341793717 n with h10 | h10
          · -- n > 18446341793717
            rcases Nat.lt_or_ge 18491991622669 n with h12 | h12
            · -- n > 18491991622669
              exact RamareSaouter2003.prime_interval_nat_ladder_c03081 n (by omega) (by omega)
            · -- n <= 18491991622669
              exact RamareSaouter2003.prime_interval_nat_ladder_c03080 n (by omega) (by omega)
          · -- n <= 18446341793717
            exact RamareSaouter2003.prime_interval_nat_ladder_c03079 n (by omega) (by omega)
        · -- n <= 18400804657163
          rcases Nat.lt_or_ge 18310067348987 n with h10 | h10
          · -- n > 18310067348987
            rcases Nat.lt_or_ge 18355379934739 n with h12 | h12
            · -- n > 18355379934739
              exact RamareSaouter2003.prime_interval_nat_ladder_c03078 n (by omega) (by omega)
            · -- n <= 18355379934739
              exact RamareSaouter2003.prime_interval_nat_ladder_c03077 n (by omega) (by omega)
          · -- n <= 18310067348987
            exact RamareSaouter2003.prime_interval_nat_ladder_c03076 n (by omega) (by omega)
  · -- n <= 18264866623151
    rcases Nat.lt_or_ge 17687311716967 n with h4 | h4
    · -- n > 17687311716967
      rcases Nat.lt_or_ge 17951570508337 n with h6 | h6
      · -- n > 17951570508337
        rcases Nat.lt_or_ge 18085176805777 n with h8 | h8
        · -- n > 18085176805777
          rcases Nat.lt_or_ge 18174799647163 n with h10 | h10
          · -- n > 18174799647163
            rcases Nat.lt_or_ge 18219777481007 n with h12 | h12
            · -- n > 18219777481007
              exact RamareSaouter2003.prime_interval_nat_ladder_c03075 n (by omega) (by omega)
            · -- n <= 18219777481007
              exact RamareSaouter2003.prime_interval_nat_ladder_c03074 n (by omega) (by omega)
          · -- n <= 18174799647163
            rcases Nat.lt_or_ge 18129932846801 n with h12 | h12
            · -- n > 18129932846801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03073 n (by omega) (by omega)
            · -- n <= 18129932846801
              exact RamareSaouter2003.prime_interval_nat_ladder_c03072 n (by omega) (by omega)
        · -- n <= 18085176805777
          rcases Nat.lt_or_ge 17995995908971 n with h10 | h10
          · -- n > 17995995908971
            rcases Nat.lt_or_ge 18040531250773 n with h12 | h12
            · -- n > 18040531250773
              exact RamareSaouter2003.prime_interval_nat_ladder_c03071 n (by omega) (by omega)
            · -- n <= 18040531250773
              exact RamareSaouter2003.prime_interval_nat_ladder_c03070 n (by omega) (by omega)
          · -- n <= 17995995908971
            exact RamareSaouter2003.prime_interval_nat_ladder_c03069 n (by omega) (by omega)
      · -- n <= 17951570508337
        rcases Nat.lt_or_ge 17818951242853 n with h8 | h8
        · -- n > 17818951242853
          rcases Nat.lt_or_ge 17863048445563 n with h10 | h10
          · -- n > 17863048445563
            rcases Nat.lt_or_ge 17907254777389 n with h12 | h12
            · -- n > 17907254777389
              exact RamareSaouter2003.prime_interval_nat_ladder_c03068 n (by omega) (by omega)
            · -- n <= 17907254777389
              exact RamareSaouter2003.prime_interval_nat_ladder_c03067 n (by omega) (by omega)
          · -- n <= 17863048445563
            exact RamareSaouter2003.prime_interval_nat_ladder_c03066 n (by omega) (by omega)
        · -- n <= 17818951242853
          rcases Nat.lt_or_ge 17731083146801 n with h10 | h10
          · -- n > 17731083146801
            rcases Nat.lt_or_ge 17774962899427 n with h12 | h12
            · -- n > 17774962899427
              exact RamareSaouter2003.prime_interval_nat_ladder_c03065 n (by omega) (by omega)
            · -- n <= 17774962899427
              exact RamareSaouter2003.prime_interval_nat_ladder_c03064 n (by omega) (by omega)
          · -- n <= 17731083146801
            exact RamareSaouter2003.prime_interval_nat_ladder_c03063 n (by omega) (by omega)
    · -- n <= 17687311716967
      rcases Nat.lt_or_ge 17426942986637 n with h6 | h6
      · -- n > 17426942986637
        rcases Nat.lt_or_ge 17556644693053 n with h8 | h8
        · -- n > 17556644693053
          rcases Nat.lt_or_ge 17600092756471 n with h10 | h10
          · -- n > 17600092756471
            rcases Nat.lt_or_ge 17643648342401 n with h12 | h12
            · -- n > 17643648342401
              exact RamareSaouter2003.prime_interval_nat_ladder_c03062 n (by omega) (by omega)
            · -- n <= 17643648342401
              exact RamareSaouter2003.prime_interval_nat_ladder_c03061 n (by omega) (by omega)
          · -- n <= 17600092756471
            exact RamareSaouter2003.prime_interval_nat_ladder_c03060 n (by omega) (by omega)
        · -- n <= 17556644693053
          rcases Nat.lt_or_ge 17470070072591 n with h10 | h10
          · -- n > 17470070072591
            rcases Nat.lt_or_ge 17513303886719 n with h12 | h12
            · -- n > 17513303886719
              exact RamareSaouter2003.prime_interval_nat_ladder_c03059 n (by omega) (by omega)
            · -- n <= 17513303886719
              exact RamareSaouter2003.prime_interval_nat_ladder_c03058 n (by omega) (by omega)
          · -- n <= 17470070072591
            exact RamareSaouter2003.prime_interval_nat_ladder_c03057 n (by omega) (by omega)
      · -- n <= 17426942986637
        rcases Nat.lt_or_ge 17298199466293 n with h8 | h8
        · -- n > 17298199466293
          rcases Nat.lt_or_ge 17341007945983 n with h10 | h10
          · -- n > 17341007945983
            rcases Nat.lt_or_ge 17383922365387 n with h12 | h12
            · -- n > 17383922365387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03056 n (by omega) (by omega)
            · -- n <= 17383922365387
              exact RamareSaouter2003.prime_interval_nat_ladder_c03055 n (by omega) (by omega)
          · -- n <= 17341007945983
            exact RamareSaouter2003.prime_interval_nat_ladder_c03054 n (by omega) (by omega)
        · -- n <= 17298199466293
          rcases Nat.lt_or_ge 17212899280439 n with h10 | h10
          · -- n > 17212899280439
            rcases Nat.lt_or_ge 17255496664727 n with h12 | h12
            · -- n > 17255496664727
              exact RamareSaouter2003.prime_interval_nat_ladder_c03053 n (by omega) (by omega)
            · -- n <= 17255496664727
              exact RamareSaouter2003.prime_interval_nat_ladder_c03052 n (by omega) (by omega)
          · -- n <= 17212899280439
            exact RamareSaouter2003.prime_interval_nat_ladder_c03051 n (by omega) (by omega)
