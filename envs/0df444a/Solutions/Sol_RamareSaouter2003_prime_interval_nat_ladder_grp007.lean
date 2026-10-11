-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp007
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T17:35:26.00752+00:00
-- url     : https://prove2.me/submissions/56ab2cba-c607-4a47-972c-cf4b99a88e73

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00301
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00302
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00303
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00304
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00305
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00306
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00307
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00308
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00309
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00310
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00311
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00312
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00313
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00314
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00315
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00316
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00317
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00318
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00319
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00320
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00321
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00322
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00323
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00324
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00325
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00326
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00327
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00328
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00329
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00330
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00331
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00332
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00333
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00334
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00335
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00336
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00337
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00338
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00339
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00340
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00341
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00342
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00343
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00344
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00345
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00346
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00347
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00348
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00349
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00350

theorem solution (n : Nat)
    (hn : 20638678393 < n) (hupper : n <= 23060765993) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 21814640767 n with h2 | h2
  · -- n > 21814640767
    rcases Nat.lt_or_ge 22403762077 n with h4 | h4
    · -- n > 22403762077
      rcases Nat.lt_or_ge 22704531281 n with h6 | h6
      · -- n > 22704531281
        rcases Nat.lt_or_ge 22856494303 n with h8 | h8
        · -- n > 22856494303
          rcases Nat.lt_or_ge 22958392871 n with h10 | h10
          · -- n > 22958392871
            rcases Nat.lt_or_ge 23009520007 n with h12 | h12
            · -- n > 23009520007
              exact RamareSaouter2003.prime_interval_nat_ladder_c00350 n (by omega) (by omega)
            · -- n <= 23009520007
              exact RamareSaouter2003.prime_interval_nat_ladder_c00349 n (by omega) (by omega)
          · -- n <= 22958392871
            rcases Nat.lt_or_ge 22907384449 n with h12 | h12
            · -- n > 22907384449
              exact RamareSaouter2003.prime_interval_nat_ladder_c00348 n (by omega) (by omega)
            · -- n <= 22907384449
              exact RamareSaouter2003.prime_interval_nat_ladder_c00347 n (by omega) (by omega)
        · -- n <= 22856494303
          rcases Nat.lt_or_ge 22755068087 n with h10 | h10
          · -- n > 22755068087
            rcases Nat.lt_or_ge 22805722339 n with h12 | h12
            · -- n > 22805722339
              exact RamareSaouter2003.prime_interval_nat_ladder_c00346 n (by omega) (by omega)
            · -- n <= 22805722339
              exact RamareSaouter2003.prime_interval_nat_ladder_c00345 n (by omega) (by omega)
          · -- n <= 22755068087
            exact RamareSaouter2003.prime_interval_nat_ladder_c00344 n (by omega) (by omega)
      · -- n <= 22704531281
        rcases Nat.lt_or_ge 22553623033 n with h8 | h8
        · -- n > 22553623033
          rcases Nat.lt_or_ge 22603809049 n with h10 | h10
          · -- n > 22603809049
            rcases Nat.lt_or_ge 22654111691 n with h12 | h12
            · -- n > 22654111691
              exact RamareSaouter2003.prime_interval_nat_ladder_c00343 n (by omega) (by omega)
            · -- n <= 22654111691
              exact RamareSaouter2003.prime_interval_nat_ladder_c00342 n (by omega) (by omega)
          · -- n <= 22603809049
            exact RamareSaouter2003.prime_interval_nat_ladder_c00341 n (by omega) (by omega)
        · -- n <= 22553623033
          rcases Nat.lt_or_ge 22453599841 n with h10 | h10
          · -- n > 22453599841
            rcases Nat.lt_or_ge 22503553409 n with h12 | h12
            · -- n > 22503553409
              exact RamareSaouter2003.prime_interval_nat_ladder_c00340 n (by omega) (by omega)
            · -- n <= 22503553409
              exact RamareSaouter2003.prime_interval_nat_ladder_c00339 n (by omega) (by omega)
          · -- n <= 22453599841
            exact RamareSaouter2003.prime_interval_nat_ladder_c00338 n (by omega) (by omega)
    · -- n <= 22403762077
      rcases Nat.lt_or_ge 22107151823 n with h6 | h6
      · -- n > 22107151823
        rcases Nat.lt_or_ge 22254940823 n with h8 | h8
        · -- n > 22254940823
          rcases Nat.lt_or_ge 22304432831 n with h10 | h10
          · -- n > 22304432831
            rcases Nat.lt_or_ge 22354039817 n with h12 | h12
            · -- n > 22354039817
              exact RamareSaouter2003.prime_interval_nat_ladder_c00337 n (by omega) (by omega)
            · -- n <= 22354039817
              exact RamareSaouter2003.prime_interval_nat_ladder_c00336 n (by omega) (by omega)
          · -- n <= 22304432831
            exact RamareSaouter2003.prime_interval_nat_ladder_c00335 n (by omega) (by omega)
        · -- n <= 22254940823
          rcases Nat.lt_or_ge 22156300609 n with h10 | h10
          · -- n > 22156300609
            rcases Nat.lt_or_ge 22205563481 n with h12 | h12
            · -- n > 22205563481
              exact RamareSaouter2003.prime_interval_nat_ladder_c00334 n (by omega) (by omega)
            · -- n <= 22205563481
              exact RamareSaouter2003.prime_interval_nat_ladder_c00333 n (by omega) (by omega)
          · -- n <= 22156300609
            exact RamareSaouter2003.prime_interval_nat_ladder_c00332 n (by omega) (by omega)
      · -- n <= 22107151823
        rcases Nat.lt_or_ge 21960387643 n with h8 | h8
        · -- n > 21960387643
          rcases Nat.lt_or_ge 22009195669 n with h10 | h10
          · -- n > 22009195669
            rcases Nat.lt_or_ge 22058116933 n with h12 | h12
            · -- n > 22058116933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00331 n (by omega) (by omega)
            · -- n <= 22058116933
              exact RamareSaouter2003.prime_interval_nat_ladder_c00330 n (by omega) (by omega)
          · -- n <= 22009195669
            exact RamareSaouter2003.prime_interval_nat_ladder_c00329 n (by omega) (by omega)
        · -- n <= 21960387643
          rcases Nat.lt_or_ge 21863110501 n with h10 | h10
          · -- n > 21863110501
            rcases Nat.lt_or_ge 21911692711 n with h12 | h12
            · -- n > 21911692711
              exact RamareSaouter2003.prime_interval_nat_ladder_c00328 n (by omega) (by omega)
            · -- n <= 21911692711
              exact RamareSaouter2003.prime_interval_nat_ladder_c00327 n (by omega) (by omega)
          · -- n <= 21863110501
            exact RamareSaouter2003.prime_interval_nat_ladder_c00326 n (by omega) (by omega)
  · -- n <= 21814640767
    rcases Nat.lt_or_ge 21194649461 n with h4 | h4
    · -- n > 21194649461
      rcases Nat.lt_or_ge 21478480081 n with h6 | h6
      · -- n > 21478480081
        rcases Nat.lt_or_ge 21621881557 n with h8 | h8
        · -- n > 21621881557
          rcases Nat.lt_or_ge 21718037867 n with h10 | h10
          · -- n > 21718037867
            rcases Nat.lt_or_ge 21766283347 n with h12 | h12
            · -- n > 21766283347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00325 n (by omega) (by omega)
            · -- n <= 21766283347
              exact RamareSaouter2003.prime_interval_nat_ladder_c00324 n (by omega) (by omega)
          · -- n <= 21718037867
            rcases Nat.lt_or_ge 21669904013 n with h12 | h12
            · -- n > 21669904013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00323 n (by omega) (by omega)
            · -- n <= 21669904013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00322 n (by omega) (by omega)
        · -- n <= 21621881557
          rcases Nat.lt_or_ge 21526169881 n with h10 | h10
          · -- n > 21526169881
            rcases Nat.lt_or_ge 21573970273 n with h12 | h12
            · -- n > 21573970273
              exact RamareSaouter2003.prime_interval_nat_ladder_c00321 n (by omega) (by omega)
            · -- n <= 21573970273
              exact RamareSaouter2003.prime_interval_nat_ladder_c00320 n (by omega) (by omega)
          · -- n <= 21526169881
            exact RamareSaouter2003.prime_interval_nat_ladder_c00319 n (by omega) (by omega)
      · -- n <= 21478480081
        rcases Nat.lt_or_ge 21336071807 n with h8 | h8
        · -- n > 21336071807
          rcases Nat.lt_or_ge 21383431339 n with h10 | h10
          · -- n > 21383431339
            rcases Nat.lt_or_ge 21430900727 n with h12 | h12
            · -- n > 21430900727
              exact RamareSaouter2003.prime_interval_nat_ladder_c00318 n (by omega) (by omega)
            · -- n <= 21430900727
              exact RamareSaouter2003.prime_interval_nat_ladder_c00317 n (by omega) (by omega)
          · -- n <= 21383431339
            exact RamareSaouter2003.prime_interval_nat_ladder_c00316 n (by omega) (by omega)
        · -- n <= 21336071807
          rcases Nat.lt_or_ge 21241681159 n with h10 | h10
          · -- n > 21241681159
            rcases Nat.lt_or_ge 21288821861 n with h12 | h12
            · -- n > 21288821861
              exact RamareSaouter2003.prime_interval_nat_ladder_c00315 n (by omega) (by omega)
            · -- n <= 21288821861
              exact RamareSaouter2003.prime_interval_nat_ladder_c00314 n (by omega) (by omega)
          · -- n <= 21241681159
            exact RamareSaouter2003.prime_interval_nat_ladder_c00313 n (by omega) (by omega)
    · -- n <= 21194649461
      rcases Nat.lt_or_ge 20914734251 n with h6 | h6
      · -- n > 20914734251
        rcases Nat.lt_or_ge 21054205981 n with h8 | h8
        · -- n > 21054205981
          rcases Nat.lt_or_ge 21100912171 n with h10 | h10
          · -- n > 21100912171
            rcases Nat.lt_or_ge 21147726583 n with h12 | h12
            · -- n > 21147726583
              exact RamareSaouter2003.prime_interval_nat_ladder_c00312 n (by omega) (by omega)
            · -- n <= 21147726583
              exact RamareSaouter2003.prime_interval_nat_ladder_c00311 n (by omega) (by omega)
          · -- n <= 21100912171
            exact RamareSaouter2003.prime_interval_nat_ladder_c00310 n (by omega) (by omega)
        · -- n <= 21054205981
          rcases Nat.lt_or_ge 20961117277 n with h10 | h10
          · -- n > 20961117277
            rcases Nat.lt_or_ge 21007607767 n with h12 | h12
            · -- n > 21007607767
              exact RamareSaouter2003.prime_interval_nat_ladder_c00309 n (by omega) (by omega)
            · -- n <= 21007607767
              exact RamareSaouter2003.prime_interval_nat_ladder_c00308 n (by omega) (by omega)
          · -- n <= 20961117277
            exact RamareSaouter2003.prime_interval_nat_ladder_c00307 n (by omega) (by omega)
      · -- n <= 20914734251
        rcases Nat.lt_or_ge 20776227361 n with h8 | h8
        · -- n > 20776227361
          rcases Nat.lt_or_ge 20822289517 n with h10 | h10
          · -- n > 20822289517
            rcases Nat.lt_or_ge 20868458411 n with h12 | h12
            · -- n > 20868458411
              exact RamareSaouter2003.prime_interval_nat_ladder_c00306 n (by omega) (by omega)
            · -- n <= 20868458411
              exact RamareSaouter2003.prime_interval_nat_ladder_c00305 n (by omega) (by omega)
          · -- n <= 20822289517
            exact RamareSaouter2003.prime_interval_nat_ladder_c00304 n (by omega) (by omega)
        · -- n <= 20776227361
          rcases Nat.lt_or_ge 20684422081 n with h10 | h10
          · -- n > 20684422081
            rcases Nat.lt_or_ge 20730271589 n with h12 | h12
            · -- n > 20730271589
              exact RamareSaouter2003.prime_interval_nat_ladder_c00303 n (by omega) (by omega)
            · -- n <= 20730271589
              exact RamareSaouter2003.prime_interval_nat_ladder_c00302 n (by omega) (by omega)
          · -- n <= 20684422081
            exact RamareSaouter2003.prime_interval_nat_ladder_c00301 n (by omega) (by omega)
