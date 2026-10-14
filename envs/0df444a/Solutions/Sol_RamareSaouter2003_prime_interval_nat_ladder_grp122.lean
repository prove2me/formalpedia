-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp122
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T20:29:03.161077+00:00
-- url     : https://prove2.me/submissions/42a108b8-2259-4183-9fd7-4e47e90dcd03

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06051
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06052
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06053
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06054
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06055
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06056
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06057
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06058
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06059
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06060
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06061
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06062
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06063
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06064
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06065
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06066
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06067
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06068
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06069
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06070
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06071
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06072
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06073
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06074
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06075
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06076
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06077
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06078
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06079
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06080
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06081
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06082
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06083
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06084
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06085
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06086
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06087
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06088
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06089
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06090
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06091
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06092
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06093
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06094
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06095
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06096
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06097
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06098
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06099
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06100

theorem solution (n : Nat)
    (hn : 60561120261956563 < n) (hupper : n <= 69756529594900877) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 64996348123618231 n with h2 | h2
  · -- n > 64996348123618231
    rcases Nat.lt_or_ge 67239243324550217 n with h4 | h4
    · -- n > 67239243324550217
      rcases Nat.lt_or_ge 68389584137515141 n with h6 | h6
      · -- n > 68389584137515141
        rcases Nat.lt_or_ge 68972105280885133 n with h8 | h8
        · -- n > 68972105280885133
          rcases Nat.lt_or_ge 69363214657717457 n with h10 | h10
          · -- n > 69363214657717457
            rcases Nat.lt_or_ge 69559592814234469 n with h12 | h12
            · -- n > 69559592814234469
              exact RamareSaouter2003.prime_interval_nat_ladder_c06100 n (by omega) (by omega)
            · -- n <= 69559592814234469
              exact RamareSaouter2003.prime_interval_nat_ladder_c06099 n (by omega) (by omega)
          · -- n <= 69363214657717457
            rcases Nat.lt_or_ge 69167383424118659 n with h12 | h12
            · -- n > 69167383424118659
              exact RamareSaouter2003.prime_interval_nat_ladder_c06098 n (by omega) (by omega)
            · -- n <= 69167383424118659
              exact RamareSaouter2003.prime_interval_nat_ladder_c06097 n (by omega) (by omega)
        · -- n <= 68972105280885133
          rcases Nat.lt_or_ge 68583211530694361 n with h10 | h10
          · -- n > 68583211530694361
            rcases Nat.lt_or_ge 68777388528762787 n with h12 | h12
            · -- n > 68777388528762787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06096 n (by omega) (by omega)
            · -- n <= 68777388528762787
              exact RamareSaouter2003.prime_interval_nat_ladder_c06095 n (by omega) (by omega)
          · -- n <= 68583211530694361
            exact RamareSaouter2003.prime_interval_nat_ladder_c06094 n (by omega) (by omega)
      · -- n <= 68389584137515141
        rcases Nat.lt_or_ge 67811967606190261 n with h8 | h8
        · -- n > 67811967606190261
          rcases Nat.lt_or_ge 68003960458315117 n with h10 | h10
          · -- n > 68003960458315117
            rcases Nat.lt_or_ge 68196498915789793 n with h12 | h12
            · -- n > 68196498915789793
              exact RamareSaouter2003.prime_interval_nat_ladder_c06093 n (by omega) (by omega)
            · -- n <= 68196498915789793
              exact RamareSaouter2003.prime_interval_nat_ladder_c06092 n (by omega) (by omega)
          · -- n <= 68003960458315117
            exact RamareSaouter2003.prime_interval_nat_ladder_c06091 n (by omega) (by omega)
        · -- n <= 67811967606190261
          rcases Nat.lt_or_ge 67429606798973183 n with h10 | h10
          · -- n > 67429606798973183
            rcases Nat.lt_or_ge 67620516605135189 n with h12 | h12
            · -- n > 67620516605135189
              exact RamareSaouter2003.prime_interval_nat_ladder_c06090 n (by omega) (by omega)
            · -- n <= 67620516605135189
              exact RamareSaouter2003.prime_interval_nat_ladder_c06089 n (by omega) (by omega)
          · -- n <= 67429606798973183
            exact RamareSaouter2003.prime_interval_nat_ladder_c06088 n (by omega) (by omega)
    · -- n <= 67239243324550217
      rcases Nat.lt_or_ge 66108287459192591 n with h6 | h6
      · -- n > 66108287459192591
        rcases Nat.lt_or_ge 66671365189269259 n with h8 | h8
        · -- n > 66671365189269259
          rcases Nat.lt_or_ge 66860131923925969 n with h10 | h10
          · -- n > 66860131923925969
            rcases Nat.lt_or_ge 67049425944956321 n with h12 | h12
            · -- n > 67049425944956321
              exact RamareSaouter2003.prime_interval_nat_ladder_c06087 n (by omega) (by omega)
            · -- n <= 67049425944956321
              exact RamareSaouter2003.prime_interval_nat_ladder_c06086 n (by omega) (by omega)
          · -- n <= 66860131923925969
            exact RamareSaouter2003.prime_interval_nat_ladder_c06085 n (by omega) (by omega)
        · -- n <= 66671365189269259
          rcases Nat.lt_or_ge 66295452093006049 n with h10 | h10
          · -- n > 66295452093006049
            rcases Nat.lt_or_ge 66483142229433443 n with h12 | h12
            · -- n > 66483142229433443
              exact RamareSaouter2003.prime_interval_nat_ladder_c06084 n (by omega) (by omega)
            · -- n <= 66483142229433443
              exact RamareSaouter2003.prime_interval_nat_ladder_c06083 n (by omega) (by omega)
          · -- n <= 66295452093006049
            exact RamareSaouter2003.prime_interval_nat_ladder_c06082 n (by omega) (by omega)
      · -- n <= 66108287459192591
        rcases Nat.lt_or_ge 65549953521732041 n with h8 | h8
        · -- n > 65549953521732041
          rcases Nat.lt_or_ge 65735535432455221 n with h10 | h10
          · -- n > 65735535432455221
            rcases Nat.lt_or_ge 65921651858426993 n with h12 | h12
            · -- n > 65921651858426993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06081 n (by omega) (by omega)
            · -- n <= 65921651858426993
              exact RamareSaouter2003.prime_interval_nat_ladder_c06080 n (by omega) (by omega)
          · -- n <= 65735535432455221
            exact RamareSaouter2003.prime_interval_nat_ladder_c06079 n (by omega) (by omega)
        · -- n <= 65549953521732041
          rcases Nat.lt_or_ge 65180353297960391 n with h10 | h10
          · -- n > 65180353297960391
            rcases Nat.lt_or_ge 65364891124289917 n with h12 | h12
            · -- n > 65364891124289917
              exact RamareSaouter2003.prime_interval_nat_ladder_c06078 n (by omega) (by omega)
            · -- n <= 65364891124289917
              exact RamareSaouter2003.prime_interval_nat_ladder_c06077 n (by omega) (by omega)
          · -- n <= 65180353297960391
            exact RamareSaouter2003.prime_interval_nat_ladder_c06076 n (by omega) (by omega)
  · -- n <= 64996348123618231
    rcases Nat.lt_or_ge 62650913598565913 n with h4 | h4
    · -- n > 62650913598565913
      rcases Nat.lt_or_ge 63722713798929739 n with h6 | h6
      · -- n > 63722713798929739
        rcases Nat.lt_or_ge 64265467871960903 n with h8 | h8
        · -- n > 64265467871960903
          rcases Nat.lt_or_ge 64629860348061857 n with h10 | h10
          · -- n > 64629860348061857
            rcases Nat.lt_or_ge 64812844875478823 n with h12 | h12
            · -- n > 64812844875478823
              exact RamareSaouter2003.prime_interval_nat_ladder_c06075 n (by omega) (by omega)
            · -- n <= 64812844875478823
              exact RamareSaouter2003.prime_interval_nat_ladder_c06074 n (by omega) (by omega)
          · -- n <= 64629860348061857
            rcases Nat.lt_or_ge 64447399501635979 n with h12 | h12
            · -- n > 64447399501635979
              exact RamareSaouter2003.prime_interval_nat_ladder_c06073 n (by omega) (by omega)
            · -- n <= 64447399501635979
              exact RamareSaouter2003.prime_interval_nat_ladder_c06072 n (by omega) (by omega)
        · -- n <= 64265467871960903
          rcases Nat.lt_or_ge 63903125322254893 n with h10 | h10
          · -- n > 63903125322254893
            rcases Nat.lt_or_ge 64084043503322561 n with h12 | h12
            · -- n > 64084043503322561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06071 n (by omega) (by omega)
            · -- n <= 64084043503322561
              exact RamareSaouter2003.prime_interval_nat_ladder_c06070 n (by omega) (by omega)
          · -- n <= 63903125322254893
            exact RamareSaouter2003.prime_interval_nat_ladder_c06069 n (by omega) (by omega)
      · -- n <= 63722713798929739
        rcases Nat.lt_or_ge 63184542742178677 n with h8 | h8
        · -- n > 63184542742178677
          rcases Nat.lt_or_ge 63363426119211121 n with h10 | h10
          · -- n > 63363426119211121
            rcases Nat.lt_or_ge 63542815442155919 n with h12 | h12
            · -- n > 63542815442155919
              exact RamareSaouter2003.prime_interval_nat_ladder_c06068 n (by omega) (by omega)
            · -- n <= 63542815442155919
              exact RamareSaouter2003.prime_interval_nat_ladder_c06067 n (by omega) (by omega)
          · -- n <= 63363426119211121
            exact RamareSaouter2003.prime_interval_nat_ladder_c06066 n (by omega) (by omega)
        · -- n <= 63184542742178677
          rcases Nat.lt_or_ge 62828297084941189 n with h10 | h10
          · -- n > 62828297084941189
            rcases Nat.lt_or_ge 63006177304667921 n with h12 | h12
            · -- n > 63006177304667921
              exact RamareSaouter2003.prime_interval_nat_ladder_c06065 n (by omega) (by omega)
            · -- n <= 63006177304667921
              exact RamareSaouter2003.prime_interval_nat_ladder_c06064 n (by omega) (by omega)
          · -- n <= 62828297084941189
            exact RamareSaouter2003.prime_interval_nat_ladder_c06063 n (by omega) (by omega)
    · -- n <= 62650913598565913
      rcases Nat.lt_or_ge 61597109338623431 n with h6 | h6
      · -- n > 61597109338623431
        rcases Nat.lt_or_ge 62121785105651191 n with h8 | h8
        · -- n > 62121785105651191
          rcases Nat.lt_or_ge 62297670176331131 n with h10 | h10
          · -- n > 62297670176331131
            rcases Nat.lt_or_ge 62474033829907937 n with h12 | h12
            · -- n > 62474033829907937
              exact RamareSaouter2003.prime_interval_nat_ladder_c06062 n (by omega) (by omega)
            · -- n <= 62474033829907937
              exact RamareSaouter2003.prime_interval_nat_ladder_c06061 n (by omega) (by omega)
          · -- n <= 62297670176331131
            exact RamareSaouter2003.prime_interval_nat_ladder_c06060 n (by omega) (by omega)
        · -- n <= 62121785105651191
          rcases Nat.lt_or_ge 61771504013285603 n with h10 | h10
          · -- n > 61771504013285603
            rcases Nat.lt_or_ge 61946397058947827 n with h12 | h12
            · -- n > 61946397058947827
              exact RamareSaouter2003.prime_interval_nat_ladder_c06059 n (by omega) (by omega)
            · -- n <= 61946397058947827
              exact RamareSaouter2003.prime_interval_nat_ladder_c06058 n (by omega) (by omega)
          · -- n <= 61771504013285603
            exact RamareSaouter2003.prime_interval_nat_ladder_c06057 n (by omega) (by omega)
      · -- n <= 61597109338623431
        rcases Nat.lt_or_ge 61076938277168599 n with h8 | h8
        · -- n > 61076938277168599
          rcases Nat.lt_or_ge 61249855545835757 n with h10 | h10
          · -- n > 61249855545835757
            rcases Nat.lt_or_ge 61423244744169409 n with h12 | h12
            · -- n > 61423244744169409
              exact RamareSaouter2003.prime_interval_nat_ladder_c06056 n (by omega) (by omega)
            · -- n <= 61423244744169409
              exact RamareSaouter2003.prime_interval_nat_ladder_c06055 n (by omega) (by omega)
          · -- n <= 61249855545835757
            exact RamareSaouter2003.prime_interval_nat_ladder_c06054 n (by omega) (by omega)
        · -- n <= 61076938277168599
          rcases Nat.lt_or_ge 60732586217941307 n with h10 | h10
          · -- n > 60732586217941307
            rcases Nat.lt_or_ge 60904520101672217 n with h12 | h12
            · -- n > 60904520101672217
              exact RamareSaouter2003.prime_interval_nat_ladder_c06053 n (by omega) (by omega)
            · -- n <= 60904520101672217
              exact RamareSaouter2003.prime_interval_nat_ladder_c06052 n (by omega) (by omega)
          · -- n <= 60732586217941307
            exact RamareSaouter2003.prime_interval_nat_ladder_c06051 n (by omega) (by omega)
