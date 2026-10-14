-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp047
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T18:25:33.108338+00:00
-- url     : https://prove2.me/submissions/c8616e57-6a77-4368-845d-f7a75ff4f71e

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02350

theorem solution (n : Nat)
    (hn : 2681425988221 < n) (hupper : n <= 3042386133557) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2856252699667 n with h2 | h2
  · -- n > 2856252699667
    rcases Nat.lt_or_ge 2944150766059 n with h4 | h4
    · -- n > 2944150766059
      rcases Nat.lt_or_ge 2989103373257 n with h6 | h6
      · -- n > 2989103373257
        rcases Nat.lt_or_ge 3011834987443 n with h8 | h8
        · -- n > 3011834987443
          rcases Nat.lt_or_ge 3027084825559 n with h10 | h10
          · -- n > 3027084825559
            rcases Nat.lt_or_ge 3034730287891 n with h12 | h12
            · -- n > 3034730287891
              exact RamareSaouter2003.prime_interval_nat_ladder_c02350 n (by omega) (by omega)
            · -- n <= 3034730287891
              exact RamareSaouter2003.prime_interval_nat_ladder_c02349 n (by omega) (by omega)
          · -- n <= 3027084825559
            rcases Nat.lt_or_ge 3019450331813 n with h12 | h12
            · -- n > 3019450331813
              exact RamareSaouter2003.prime_interval_nat_ladder_c02348 n (by omega) (by omega)
            · -- n <= 3019450331813
              exact RamareSaouter2003.prime_interval_nat_ladder_c02347 n (by omega) (by omega)
        · -- n <= 3011834987443
          rcases Nat.lt_or_ge 2996661555739 n with h10 | h10
          · -- n > 2996661555739
            rcases Nat.lt_or_ge 3004238744641 n with h12 | h12
            · -- n > 3004238744641
              exact RamareSaouter2003.prime_interval_nat_ladder_c02346 n (by omega) (by omega)
            · -- n <= 3004238744641
              exact RamareSaouter2003.prime_interval_nat_ladder_c02345 n (by omega) (by omega)
          · -- n <= 2996661555739
            exact RamareSaouter2003.prime_interval_nat_ladder_c02344 n (by omega) (by omega)
      · -- n <= 2989103373257
        rcases Nat.lt_or_ge 2966542390789 n with h8 | h8
        · -- n > 2966542390789
          rcases Nat.lt_or_ge 2974043838001 n with h10 | h10
          · -- n > 2974043838001
            rcases Nat.lt_or_ge 2981564149819 n with h12 | h12
            · -- n > 2981564149819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02343 n (by omega) (by omega)
            · -- n <= 2981564149819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02342 n (by omega) (by omega)
          · -- n <= 2974043838001
            exact RamareSaouter2003.prime_interval_nat_ladder_c02341 n (by omega) (by omega)
        · -- n <= 2966542390789
          rcases Nat.lt_or_ge 2951595901693 n with h10 | h10
          · -- n > 2951595901693
            rcases Nat.lt_or_ge 2959059760981 n with h12 | h12
            · -- n > 2959059760981
              exact RamareSaouter2003.prime_interval_nat_ladder_c02340 n (by omega) (by omega)
            · -- n <= 2959059760981
              exact RamareSaouter2003.prime_interval_nat_ladder_c02339 n (by omega) (by omega)
          · -- n <= 2951595901693
            exact RamareSaouter2003.prime_interval_nat_ladder_c02338 n (by omega) (by omega)
    · -- n <= 2944150766059
      rcases Nat.lt_or_ge 2899870542311 n with h6 | h6
      · -- n > 2899870542311
        rcases Nat.lt_or_ge 2921927234983 n with h8 | h8
        · -- n > 2921927234983
          rcases Nat.lt_or_ge 2929316479301 n with h10 | h10
          · -- n > 2929316479301
            rcases Nat.lt_or_ge 2936724307537 n with h12 | h12
            · -- n > 2936724307537
              exact RamareSaouter2003.prime_interval_nat_ladder_c02337 n (by omega) (by omega)
            · -- n <= 2936724307537
              exact RamareSaouter2003.prime_interval_nat_ladder_c02336 n (by omega) (by omega)
          · -- n <= 2929316479301
            exact RamareSaouter2003.prime_interval_nat_ladder_c02335 n (by omega) (by omega)
        · -- n <= 2921927234983
          rcases Nat.lt_or_ge 2907204312671 n with h10 | h10
          · -- n > 2907204312671
            rcases Nat.lt_or_ge 2914556528167 n with h12 | h12
            · -- n > 2914556528167
              exact RamareSaouter2003.prime_interval_nat_ladder_c02334 n (by omega) (by omega)
            · -- n <= 2914556528167
              exact RamareSaouter2003.prime_interval_nat_ladder_c02333 n (by omega) (by omega)
          · -- n <= 2907204312671
            exact RamareSaouter2003.prime_interval_nat_ladder_c02332 n (by omega) (by omega)
      · -- n <= 2899870542311
        rcases Nat.lt_or_ge 2877979442699 n with h8 | h8
        · -- n > 2877979442699
          rcases Nat.lt_or_ge 2885258153233 n with h10 | h10
          · -- n > 2885258153233
            rcases Nat.lt_or_ge 2892555171113 n with h12 | h12
            · -- n > 2892555171113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02331 n (by omega) (by omega)
            · -- n <= 2892555171113
              exact RamareSaouter2003.prime_interval_nat_ladder_c02330 n (by omega) (by omega)
          · -- n <= 2885258153233
            exact RamareSaouter2003.prime_interval_nat_ladder_c02329 n (by omega) (by omega)
        · -- n <= 2877979442699
          rcases Nat.lt_or_ge 2863476761477 n with h10 | h10
          · -- n > 2863476761477
            rcases Nat.lt_or_ge 2870718993937 n with h12 | h12
            · -- n > 2870718993937
              exact RamareSaouter2003.prime_interval_nat_ladder_c02328 n (by omega) (by omega)
            · -- n <= 2870718993937
              exact RamareSaouter2003.prime_interval_nat_ladder_c02327 n (by omega) (by omega)
          · -- n <= 2863476761477
            exact RamareSaouter2003.prime_interval_nat_ladder_c02326 n (by omega) (by omega)
  · -- n <= 2856252699667
    rcases Nat.lt_or_ge 2763972959471 n with h4 | h4
    · -- n > 2763972959471
      rcases Nat.lt_or_ge 2806189254469 n with h6 | h6
      · -- n > 2806189254469
        rcases Nat.lt_or_ge 2827537255141 n with h8 | h8
        · -- n > 2827537255141
          rcases Nat.lt_or_ge 2841858907171 n with h10 | h10
          · -- n > 2841858907171
            rcases Nat.lt_or_ge 2849046763291 n with h12 | h12
            · -- n > 2849046763291
              exact RamareSaouter2003.prime_interval_nat_ladder_c02325 n (by omega) (by omega)
            · -- n <= 2849046763291
              exact RamareSaouter2003.prime_interval_nat_ladder_c02324 n (by omega) (by omega)
          · -- n <= 2841858907171
            rcases Nat.lt_or_ge 2834689086197 n with h12 | h12
            · -- n > 2834689086197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02323 n (by omega) (by omega)
            · -- n <= 2834689086197
              exact RamareSaouter2003.prime_interval_nat_ladder_c02322 n (by omega) (by omega)
        · -- n <= 2827537255141
          rcases Nat.lt_or_ge 2813287384099 n with h10 | h10
          · -- n > 2813287384099
            rcases Nat.lt_or_ge 2820403369361 n with h12 | h12
            · -- n > 2820403369361
              exact RamareSaouter2003.prime_interval_nat_ladder_c02321 n (by omega) (by omega)
            · -- n <= 2820403369361
              exact RamareSaouter2003.prime_interval_nat_ladder_c02320 n (by omega) (by omega)
          · -- n <= 2813287384099
            exact RamareSaouter2003.prime_interval_nat_ladder_c02319 n (by omega) (by omega)
      · -- n <= 2806189254469
        rcases Nat.lt_or_ge 2785001554837 n with h8 | h8
        · -- n > 2785001554837
          rcases Nat.lt_or_ge 2792046384227 n with h10 | h10
          · -- n > 2792046384227
            rcases Nat.lt_or_ge 2799108935989 n with h12 | h12
            · -- n > 2799108935989
              exact RamareSaouter2003.prime_interval_nat_ladder_c02318 n (by omega) (by omega)
            · -- n <= 2799108935989
              exact RamareSaouter2003.prime_interval_nat_ladder_c02317 n (by omega) (by omega)
          · -- n <= 2792046384227
            exact RamareSaouter2003.prime_interval_nat_ladder_c02316 n (by omega) (by omega)
        · -- n <= 2785001554837
          rcases Nat.lt_or_ge 2770964886467 n with h10 | h10
          · -- n > 2770964886467
            rcases Nat.lt_or_ge 2777974403639 n with h12 | h12
            · -- n > 2777974403639
              exact RamareSaouter2003.prime_interval_nat_ladder_c02315 n (by omega) (by omega)
            · -- n <= 2777974403639
              exact RamareSaouter2003.prime_interval_nat_ladder_c02314 n (by omega) (by omega)
          · -- n <= 2770964886467
            exact RamareSaouter2003.prime_interval_nat_ladder_c02313 n (by omega) (by omega)
    · -- n <= 2763972959471
      rcases Nat.lt_or_ge 2722388337239 n with h6 | h6
      · -- n > 2722388337239
        rcases Nat.lt_or_ge 2743102280027 n with h8 | h8
        · -- n > 2743102280027
          rcases Nat.lt_or_ge 2750041699921 n with h10 | h10
          · -- n > 2750041699921
            rcases Nat.lt_or_ge 2756998578533 n with h12 | h12
            · -- n > 2756998578533
              exact RamareSaouter2003.prime_interval_nat_ladder_c02312 n (by omega) (by omega)
            · -- n <= 2756998578533
              exact RamareSaouter2003.prime_interval_nat_ladder_c02311 n (by omega) (by omega)
          · -- n <= 2750041699921
            exact RamareSaouter2003.prime_interval_nat_ladder_c02310 n (by omega) (by omega)
        · -- n <= 2743102280027
          rcases Nat.lt_or_ge 2729275642109 n with h10 | h10
          · -- n > 2729275642109
            rcases Nat.lt_or_ge 2736180275263 n with h12 | h12
            · -- n > 2736180275263
              exact RamareSaouter2003.prime_interval_nat_ladder_c02309 n (by omega) (by omega)
            · -- n <= 2736180275263
              exact RamareSaouter2003.prime_interval_nat_ladder_c02308 n (by omega) (by omega)
          · -- n <= 2729275642109
            exact RamareSaouter2003.prime_interval_nat_ladder_c02307 n (by omega) (by omega)
      · -- n <= 2722388337239
        rcases Nat.lt_or_ge 2701829960677 n with h8 | h8
        · -- n > 2701829960677
          rcases Nat.lt_or_ge 2708665539647 n with h10 | h10
          · -- n > 2708665539647
            rcases Nat.lt_or_ge 2715518317541 n with h12 | h12
            · -- n > 2715518317541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02306 n (by omega) (by omega)
            · -- n <= 2715518317541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02305 n (by omega) (by omega)
          · -- n <= 2708665539647
            exact RamareSaouter2003.prime_interval_nat_ladder_c02304 n (by omega) (by omega)
        · -- n <= 2701829960677
          rcases Nat.lt_or_ge 2688210227777 n with h10 | h10
          · -- n > 2688210227777
            rcases Nat.lt_or_ge 2695011537697 n with h12 | h12
            · -- n > 2695011537697
              exact RamareSaouter2003.prime_interval_nat_ladder_c02303 n (by omega) (by omega)
            · -- n <= 2695011537697
              exact RamareSaouter2003.prime_interval_nat_ladder_c02302 n (by omega) (by omega)
          · -- n <= 2688210227777
            exact RamareSaouter2003.prime_interval_nat_ladder_c02301 n (by omega) (by omega)
