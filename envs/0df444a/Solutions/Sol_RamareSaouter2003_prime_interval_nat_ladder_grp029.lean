-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp029
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T07:31:09.201715+00:00
-- url     : https://prove2.me/submissions/055c3074-2149-46e8-934f-9808709b055c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01450

theorem solution (n : Nat)
    (hn : 275326001903 < n) (hupper : n <= 312172099721) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 293165409577 n with h2 | h2
  · -- n > 293165409577
    rcases Nat.lt_or_ge 302138312323 n with h4 | h4
    · -- n > 302138312323
      rcases Nat.lt_or_ge 306728200087 n with h6 | h6
      · -- n > 306728200087
        rcases Nat.lt_or_ge 309049469123 n with h8 | h8
        · -- n > 309049469123
          rcases Nat.lt_or_ge 310606824043 n with h10 | h10
          · -- n > 310606824043
            rcases Nat.lt_or_ge 311388469193 n with h12 | h12
            · -- n > 311388469193
              exact RamareSaouter2003.prime_interval_nat_ladder_c01450 n (by omega) (by omega)
            · -- n <= 311388469193
              exact RamareSaouter2003.prime_interval_nat_ladder_c01449 n (by omega) (by omega)
          · -- n <= 310606824043
            rcases Nat.lt_or_ge 309827159063 n with h12 | h12
            · -- n > 309827159063
              exact RamareSaouter2003.prime_interval_nat_ladder_c01448 n (by omega) (by omega)
            · -- n <= 309827159063
              exact RamareSaouter2003.prime_interval_nat_ladder_c01447 n (by omega) (by omega)
        · -- n <= 309049469123
          rcases Nat.lt_or_ge 307499994671 n with h10 | h10
          · -- n > 307499994671
            rcases Nat.lt_or_ge 308273749451 n with h12 | h12
            · -- n > 308273749451
              exact RamareSaouter2003.prime_interval_nat_ladder_c01446 n (by omega) (by omega)
            · -- n <= 308273749451
              exact RamareSaouter2003.prime_interval_nat_ladder_c01445 n (by omega) (by omega)
          · -- n <= 307499994671
            exact RamareSaouter2003.prime_interval_nat_ladder_c01444 n (by omega) (by omega)
      · -- n <= 306728200087
        rcases Nat.lt_or_ge 304424525851 n with h8 | h8
        · -- n > 304424525851
          rcases Nat.lt_or_ge 305190470573 n with h10 | h10
          · -- n > 305190470573
            rcases Nat.lt_or_ge 305958360307 n with h12 | h12
            · -- n > 305958360307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01443 n (by omega) (by omega)
            · -- n <= 305958360307
              exact RamareSaouter2003.prime_interval_nat_ladder_c01442 n (by omega) (by omega)
          · -- n <= 305190470573
            exact RamareSaouter2003.prime_interval_nat_ladder_c01441 n (by omega) (by omega)
        · -- n <= 304424525851
          rcases Nat.lt_or_ge 302898451703 n with h10 | h10
          · -- n > 302898451703
            rcases Nat.lt_or_ge 303660521261 n with h12 | h12
            · -- n > 303660521261
              exact RamareSaouter2003.prime_interval_nat_ladder_c01440 n (by omega) (by omega)
            · -- n <= 303660521261
              exact RamareSaouter2003.prime_interval_nat_ladder_c01439 n (by omega) (by omega)
          · -- n <= 302898451703
            exact RamareSaouter2003.prime_interval_nat_ladder_c01438 n (by omega) (by omega)
    · -- n <= 302138312323
      rcases Nat.lt_or_ge 297617734331 n with h6 | h6
      · -- n > 297617734331
        rcases Nat.lt_or_ge 299869426099 n with h8 | h8
        · -- n > 299869426099
          rcases Nat.lt_or_ge 300623804357 n with h10 | h10
          · -- n > 300623804357
            rcases Nat.lt_or_ge 301380098177 n with h12 | h12
            · -- n > 301380098177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01437 n (by omega) (by omega)
            · -- n <= 301380098177
              exact RamareSaouter2003.prime_interval_nat_ladder_c01436 n (by omega) (by omega)
          · -- n <= 300623804357
            exact RamareSaouter2003.prime_interval_nat_ladder_c01435 n (by omega) (by omega)
        · -- n <= 299869426099
          rcases Nat.lt_or_ge 298366395913 n with h10 | h10
          · -- n > 298366395913
            rcases Nat.lt_or_ge 299116958221 n with h12 | h12
            · -- n > 299116958221
              exact RamareSaouter2003.prime_interval_nat_ladder_c01434 n (by omega) (by omega)
            · -- n <= 299116958221
              exact RamareSaouter2003.prime_interval_nat_ladder_c01433 n (by omega) (by omega)
          · -- n <= 298366395913
            exact RamareSaouter2003.prime_interval_nat_ladder_c01432 n (by omega) (by omega)
      · -- n <= 297617734331
        rcases Nat.lt_or_ge 295383105653 n with h8 | h8
        · -- n > 295383105653
          rcases Nat.lt_or_ge 296126093993 n with h10 | h10
          · -- n > 296126093993
            rcases Nat.lt_or_ge 296870968631 n with h12 | h12
            · -- n > 296870968631
              exact RamareSaouter2003.prime_interval_nat_ladder_c01431 n (by omega) (by omega)
            · -- n <= 296870968631
              exact RamareSaouter2003.prime_interval_nat_ladder_c01430 n (by omega) (by omega)
          · -- n <= 296126093993
            exact RamareSaouter2003.prime_interval_nat_ladder_c01429 n (by omega) (by omega)
        · -- n <= 295383105653
          rcases Nat.lt_or_ge 293902768219 n with h10 | h10
          · -- n > 293902768219
            rcases Nat.lt_or_ge 294641998627 n with h12 | h12
            · -- n > 294641998627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01428 n (by omega) (by omega)
            · -- n <= 294641998627
              exact RamareSaouter2003.prime_interval_nat_ladder_c01427 n (by omega) (by omega)
          · -- n <= 293902768219
            exact RamareSaouter2003.prime_interval_nat_ladder_c01426 n (by omega) (by omega)
  · -- n <= 293165409577
    rcases Nat.lt_or_ge 283747921229 n with h4 | h4
    · -- n > 283747921229
      rcases Nat.lt_or_ge 288055909153 n with h6 | h6
      · -- n > 288055909153
        rcases Nat.lt_or_ge 290234597491 n with h8 | h8
        · -- n > 290234597491
          rcases Nat.lt_or_ge 291696288547 n with h10 | h10
          · -- n > 291696288547
            rcases Nat.lt_or_ge 292429917937 n with h12 | h12
            · -- n > 292429917937
              exact RamareSaouter2003.prime_interval_nat_ladder_c01425 n (by omega) (by omega)
            · -- n <= 292429917937
              exact RamareSaouter2003.prime_interval_nat_ladder_c01424 n (by omega) (by omega)
          · -- n <= 291696288547
            rcases Nat.lt_or_ge 290964516671 n with h12 | h12
            · -- n > 290964516671
              exact RamareSaouter2003.prime_interval_nat_ladder_c01423 n (by omega) (by omega)
            · -- n <= 290964516671
              exact RamareSaouter2003.prime_interval_nat_ladder_c01422 n (by omega) (by omega)
        · -- n <= 290234597491
          rcases Nat.lt_or_ge 288780298459 n with h10 | h10
          · -- n > 288780298459
            rcases Nat.lt_or_ge 289506526321 n with h12 | h12
            · -- n > 289506526321
              exact RamareSaouter2003.prime_interval_nat_ladder_c01421 n (by omega) (by omega)
            · -- n <= 289506526321
              exact RamareSaouter2003.prime_interval_nat_ladder_c01420 n (by omega) (by omega)
          · -- n <= 288780298459
            exact RamareSaouter2003.prime_interval_nat_ladder_c01419 n (by omega) (by omega)
      · -- n <= 288055909153
        rcases Nat.lt_or_ge 285893725787 n with h8 | h8
        · -- n > 285893725787
          rcases Nat.lt_or_ge 286612627481 n with h10 | h10
          · -- n > 286612627481
            rcases Nat.lt_or_ge 287333353721 n with h12 | h12
            · -- n > 287333353721
              exact RamareSaouter2003.prime_interval_nat_ladder_c01418 n (by omega) (by omega)
            · -- n <= 287333353721
              exact RamareSaouter2003.prime_interval_nat_ladder_c01417 n (by omega) (by omega)
          · -- n <= 286612627481
            exact RamareSaouter2003.prime_interval_nat_ladder_c01416 n (by omega) (by omega)
        · -- n <= 285893725787
          rcases Nat.lt_or_ge 284461377289 n with h10 | h10
          · -- n > 284461377289
            rcases Nat.lt_or_ge 285176643929 n with h12 | h12
            · -- n > 285176643929
              exact RamareSaouter2003.prime_interval_nat_ladder_c01415 n (by omega) (by omega)
            · -- n <= 285176643929
              exact RamareSaouter2003.prime_interval_nat_ladder_c01414 n (by omega) (by omega)
          · -- n <= 284461377289
            exact RamareSaouter2003.prime_interval_nat_ladder_c01413 n (by omega) (by omega)
    · -- n <= 283747921229
      rcases Nat.lt_or_ge 279504948823 n with h6 | h6
      · -- n > 279504948823
        rcases Nat.lt_or_ge 281618370277 n with h8 | h8
        · -- n > 281618370277
          rcases Nat.lt_or_ge 282326422321 n with h10 | h10
          · -- n > 282326422321
            rcases Nat.lt_or_ge 283036271101 n with h12 | h12
            · -- n > 283036271101
              exact RamareSaouter2003.prime_interval_nat_ladder_c01412 n (by omega) (by omega)
            · -- n <= 283036271101
              exact RamareSaouter2003.prime_interval_nat_ladder_c01411 n (by omega) (by omega)
          · -- n <= 282326422321
            exact RamareSaouter2003.prime_interval_nat_ladder_c01410 n (by omega) (by omega)
        · -- n <= 281618370277
          rcases Nat.lt_or_ge 280207638103 n with h10 | h10
          · -- n > 280207638103
            rcases Nat.lt_or_ge 280912110377 n with h12 | h12
            · -- n > 280912110377
              exact RamareSaouter2003.prime_interval_nat_ladder_c01409 n (by omega) (by omega)
            · -- n <= 280912110377
              exact RamareSaouter2003.prime_interval_nat_ladder_c01408 n (by omega) (by omega)
          · -- n <= 280207638103
            exact RamareSaouter2003.prime_interval_nat_ladder_c01407 n (by omega) (by omega)
      · -- n <= 279504948823
        rcases Nat.lt_or_ge 277407533453 n with h8 | h8
        · -- n > 277407533453
          rcases Nat.lt_or_ge 278104901033 n with h10 | h10
          · -- n > 278104901033
            rcases Nat.lt_or_ge 278804037997 n with h12 | h12
            · -- n > 278804037997
              exact RamareSaouter2003.prime_interval_nat_ladder_c01406 n (by omega) (by omega)
            · -- n <= 278804037997
              exact RamareSaouter2003.prime_interval_nat_ladder_c01405 n (by omega) (by omega)
          · -- n <= 278104901033
            exact RamareSaouter2003.prime_interval_nat_ladder_c01404 n (by omega) (by omega)
        · -- n <= 277407533453
          rcases Nat.lt_or_ge 276018088417 n with h10 | h10
          · -- n > 276018088417
            rcases Nat.lt_or_ge 276711930769 n with h12 | h12
            · -- n > 276711930769
              exact RamareSaouter2003.prime_interval_nat_ladder_c01403 n (by omega) (by omega)
            · -- n <= 276711930769
              exact RamareSaouter2003.prime_interval_nat_ladder_c01402 n (by omega) (by omega)
          · -- n <= 276018088417
            exact RamareSaouter2003.prime_interval_nat_ladder_c01401 n (by omega) (by omega)
