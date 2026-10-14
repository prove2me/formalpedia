-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp046
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T17:47:32.055296+00:00
-- url     : https://prove2.me/submissions/e78b4c17-9a66-4319-9ba6-e3bce5710fbc

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02296
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02297
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02298
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02299
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02300

theorem solution (n : Nat)
    (hn : 2363065123879 < n) (hupper : n <= 2681425988221) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 2517245092787 n with h2 | h2
  · -- n > 2517245092787
    rcases Nat.lt_or_ge 2594765039567 n with h4 | h4
    · -- n > 2594765039567
      rcases Nat.lt_or_ge 2634410717651 n with h6 | h6
      · -- n > 2634410717651
        rcases Nat.lt_or_ge 2654458883897 n with h8 | h8
        · -- n > 2654458883897
          rcases Nat.lt_or_ge 2667908550217 n with h10 | h10
          · -- n > 2667908550217
            rcases Nat.lt_or_ge 2674658776541 n with h12 | h12
            · -- n > 2674658776541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02300 n (by omega) (by omega)
            · -- n <= 2674658776541
              exact RamareSaouter2003.prime_interval_nat_ladder_c02299 n (by omega) (by omega)
          · -- n <= 2667908550217
            rcases Nat.lt_or_ge 2661175266773 n with h12 | h12
            · -- n > 2661175266773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02298 n (by omega) (by omega)
            · -- n <= 2661175266773
              exact RamareSaouter2003.prime_interval_nat_ladder_c02297 n (by omega) (by omega)
        · -- n <= 2654458883897
          rcases Nat.lt_or_ge 2641076651399 n with h10 | h10
          · -- n > 2641076651399
            rcases Nat.lt_or_ge 2647759359521 n with h12 | h12
            · -- n > 2647759359521
              exact RamareSaouter2003.prime_interval_nat_ladder_c02296 n (by omega) (by omega)
            · -- n <= 2647759359521
              exact RamareSaouter2003.prime_interval_nat_ladder_c02295 n (by omega) (by omega)
          · -- n <= 2641076651399
            exact RamareSaouter2003.prime_interval_nat_ladder_c02294 n (by omega) (by omega)
      · -- n <= 2634410717651
        rcases Nat.lt_or_ge 2614513144597 n with h8 | h8
        · -- n > 2614513144597
          rcases Nat.lt_or_ge 2621129006071 n with h10 | h10
          · -- n > 2621129006071
            rcases Nat.lt_or_ge 2627761516607 n with h12 | h12
            · -- n > 2627761516607
              exact RamareSaouter2003.prime_interval_nat_ladder_c02293 n (by omega) (by omega)
            · -- n <= 2627761516607
              exact RamareSaouter2003.prime_interval_nat_ladder_c02292 n (by omega) (by omega)
          · -- n <= 2621129006071
            exact RamareSaouter2003.prime_interval_nat_ladder_c02291 n (by omega) (by omega)
        · -- n <= 2614513144597
          rcases Nat.lt_or_ge 2601331202801 n with h10 | h10
          · -- n > 2601331202801
            rcases Nat.lt_or_ge 2607913890737 n with h12 | h12
            · -- n > 2607913890737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02290 n (by omega) (by omega)
            · -- n <= 2607913890737
              exact RamareSaouter2003.prime_interval_nat_ladder_c02289 n (by omega) (by omega)
          · -- n <= 2601331202801
            exact RamareSaouter2003.prime_interval_nat_ladder_c02288 n (by omega) (by omega)
    · -- n <= 2594765039567
      rcases Nat.lt_or_ge 2555712776137 n with h6 | h6
      · -- n > 2555712776137
        rcases Nat.lt_or_ge 2575165286299 n with h8 | h8
        · -- n > 2575165286299
          rcases Nat.lt_or_ge 2581682122223 n with h10 | h10
          · -- n > 2581682122223
            rcases Nat.lt_or_ge 2588215359749 n with h12 | h12
            · -- n > 2588215359749
              exact RamareSaouter2003.prime_interval_nat_ladder_c02287 n (by omega) (by omega)
            · -- n <= 2588215359749
              exact RamareSaouter2003.prime_interval_nat_ladder_c02286 n (by omega) (by omega)
          · -- n <= 2581682122223
            exact RamareSaouter2003.prime_interval_nat_ladder_c02285 n (by omega) (by omega)
        · -- n <= 2575165286299
          rcases Nat.lt_or_ge 2562180653863 n with h10 | h10
          · -- n > 2562180653863
            rcases Nat.lt_or_ge 2568664810351 n with h12 | h12
            · -- n > 2568664810351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02284 n (by omega) (by omega)
            · -- n <= 2568664810351
              exact RamareSaouter2003.prime_interval_nat_ladder_c02283 n (by omega) (by omega)
          · -- n <= 2562180653863
            exact RamareSaouter2003.prime_interval_nat_ladder_c02282 n (by omega) (by omega)
      · -- n <= 2555712776137
        rcases Nat.lt_or_ge 2536406408857 n with h8 | h8
        · -- n > 2536406408857
          rcases Nat.lt_or_ge 2542825694093 n with h10 | h10
          · -- n > 2542825694093
            rcases Nat.lt_or_ge 2549261136379 n with h12 | h12
            · -- n > 2549261136379
              exact RamareSaouter2003.prime_interval_nat_ladder_c02281 n (by omega) (by omega)
            · -- n <= 2549261136379
              exact RamareSaouter2003.prime_interval_nat_ladder_c02280 n (by omega) (by omega)
          · -- n <= 2542825694093
            exact RamareSaouter2003.prime_interval_nat_ladder_c02279 n (by omega) (by omega)
        · -- n <= 2536406408857
          rcases Nat.lt_or_ge 2523616148411 n with h10 | h10
          · -- n > 2523616148411
            rcases Nat.lt_or_ge 2530003240393 n with h12 | h12
            · -- n > 2530003240393
              exact RamareSaouter2003.prime_interval_nat_ladder_c02278 n (by omega) (by omega)
            · -- n <= 2530003240393
              exact RamareSaouter2003.prime_interval_nat_ladder_c02277 n (by omega) (by omega)
          · -- n <= 2523616148411
            exact RamareSaouter2003.prime_interval_nat_ladder_c02276 n (by omega) (by omega)
  · -- n <= 2517245092787
    rcases Nat.lt_or_ge 2435862594443 n with h4 | h4
    · -- n > 2435862594443
      rcases Nat.lt_or_ge 2473093370479 n with h6 | h6
      · -- n > 2473093370479
        rcases Nat.lt_or_ge 2491920434519 n with h8 | h8
        · -- n > 2491920434519
          rcases Nat.lt_or_ge 2504550930533 n with h10 | h10
          · -- n > 2504550930533
            rcases Nat.lt_or_ge 2510890033453 n with h12 | h12
            · -- n > 2510890033453
              exact RamareSaouter2003.prime_interval_nat_ladder_c02275 n (by omega) (by omega)
            · -- n <= 2510890033453
              exact RamareSaouter2003.prime_interval_nat_ladder_c02274 n (by omega) (by omega)
          · -- n <= 2504550930533
            rcases Nat.lt_or_ge 2498227744169 n with h12 | h12
            · -- n > 2498227744169
              exact RamareSaouter2003.prime_interval_nat_ladder_c02273 n (by omega) (by omega)
            · -- n <= 2498227744169
              exact RamareSaouter2003.prime_interval_nat_ladder_c02272 n (by omega) (by omega)
        · -- n <= 2491920434519
          rcases Nat.lt_or_ge 2479353287227 n with h10 | h10
          · -- n > 2479353287227
            rcases Nat.lt_or_ge 2485628962129 n with h12 | h12
            · -- n > 2485628962129
              exact RamareSaouter2003.prime_interval_nat_ladder_c02271 n (by omega) (by omega)
            · -- n <= 2485628962129
              exact RamareSaouter2003.prime_interval_nat_ladder_c02270 n (by omega) (by omega)
          · -- n <= 2479353287227
            exact RamareSaouter2003.prime_interval_nat_ladder_c02269 n (by omega) (by omega)
      · -- n <= 2473093370479
        rcases Nat.lt_or_ge 2454407776127 n with h8 | h8
        · -- n > 2454407776127
          rcases Nat.lt_or_ge 2460620654137 n with h10 | h10
          · -- n > 2460620654137
            rcases Nat.lt_or_ge 2466849172523 n with h12 | h12
            · -- n > 2466849172523
              exact RamareSaouter2003.prime_interval_nat_ladder_c02268 n (by omega) (by omega)
            · -- n <= 2466849172523
              exact RamareSaouter2003.prime_interval_nat_ladder_c02267 n (by omega) (by omega)
          · -- n <= 2460620654137
            exact RamareSaouter2003.prime_interval_nat_ladder_c02266 n (by omega) (by omega)
        · -- n <= 2454407776127
          rcases Nat.lt_or_ge 2442028785151 n with h10 | h10
          · -- n > 2442028785151
            rcases Nat.lt_or_ge 2448210499451 n with h12 | h12
            · -- n > 2448210499451
              exact RamareSaouter2003.prime_interval_nat_ladder_c02265 n (by omega) (by omega)
            · -- n <= 2448210499451
              exact RamareSaouter2003.prime_interval_nat_ladder_c02264 n (by omega) (by omega)
          · -- n <= 2442028785151
            exact RamareSaouter2003.prime_interval_nat_ladder_c02263 n (by omega) (by omega)
    · -- n <= 2435862594443
      rcases Nat.lt_or_ge 2399189279369 n with h6 | h6
      · -- n > 2399189279369
        rcases Nat.lt_or_ge 2417456776037 n with h8 | h8
        · -- n > 2417456776037
          rcases Nat.lt_or_ge 2423576628541 n with h10 | h10
          · -- n > 2423576628541
            rcases Nat.lt_or_ge 2429711888491 n with h12 | h12
            · -- n > 2429711888491
              exact RamareSaouter2003.prime_interval_nat_ladder_c02262 n (by omega) (by omega)
            · -- n <= 2429711888491
              exact RamareSaouter2003.prime_interval_nat_ladder_c02261 n (by omega) (by omega)
          · -- n <= 2423576628541
            exact RamareSaouter2003.prime_interval_nat_ladder_c02260 n (by omega) (by omega)
        · -- n <= 2417456776037
          rcases Nat.lt_or_ge 2405263139831 n with h10 | h10
          · -- n > 2405263139831
            rcases Nat.lt_or_ge 2411352292589 n with h12 | h12
            · -- n > 2411352292589
              exact RamareSaouter2003.prime_interval_nat_ladder_c02259 n (by omega) (by omega)
            · -- n <= 2411352292589
              exact RamareSaouter2003.prime_interval_nat_ladder_c02258 n (by omega) (by omega)
          · -- n <= 2405263139831
            exact RamareSaouter2003.prime_interval_nat_ladder_c02257 n (by omega) (by omega)
      · -- n <= 2399189279369
        rcases Nat.lt_or_ge 2381059070653 n with h8 | h8
        · -- n > 2381059070653
          rcases Nat.lt_or_ge 2387087282911 n with h10 | h10
          · -- n > 2387087282911
            rcases Nat.lt_or_ge 2393130673009 n with h12 | h12
            · -- n > 2393130673009
              exact RamareSaouter2003.prime_interval_nat_ladder_c02256 n (by omega) (by omega)
            · -- n <= 2393130673009
              exact RamareSaouter2003.prime_interval_nat_ladder_c02255 n (by omega) (by omega)
          · -- n <= 2387087282911
            exact RamareSaouter2003.prime_interval_nat_ladder_c02254 n (by omega) (by omega)
        · -- n <= 2381059070653
          rcases Nat.lt_or_ge 2369048029081 n with h10 | h10
          · -- n > 2369048029081
            rcases Nat.lt_or_ge 2375045998651 n with h12 | h12
            · -- n > 2375045998651
              exact RamareSaouter2003.prime_interval_nat_ladder_c02253 n (by omega) (by omega)
            · -- n <= 2375045998651
              exact RamareSaouter2003.prime_interval_nat_ladder_c02252 n (by omega) (by omega)
          · -- n <= 2369048029081
            exact RamareSaouter2003.prime_interval_nat_ladder_c02251 n (by omega) (by omega)
