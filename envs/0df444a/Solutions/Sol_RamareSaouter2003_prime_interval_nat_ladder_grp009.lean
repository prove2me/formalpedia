-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp009
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T18:43:15.584386+00:00
-- url     : https://prove2.me/submissions/982213a9-032f-4b2b-b548-6fb6d27abcde

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00450

theorem solution (n : Nat)
    (hn : 25781257687 < n) (hupper : n <= 28838600017) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 27265225847 n with h2 | h2
  · -- n > 27265225847
    rcases Nat.lt_or_ge 28008950069 n with h4 | h4
    · -- n > 28008950069
      rcases Nat.lt_or_ge 28388725091 n with h6 | h6
      · -- n > 28388725091
        rcases Nat.lt_or_ge 28580624767 n with h8 | h8
        · -- n > 28580624767
          rcases Nat.lt_or_ge 28709309903 n with h10 | h10
          · -- n > 28709309903
            rcases Nat.lt_or_ge 28773879163 n with h12 | h12
            · -- n > 28773879163
              exact RamareSaouter2003.prime_interval_nat_ladder_c00450 n (by omega) (by omega)
            · -- n <= 28773879163
              exact RamareSaouter2003.prime_interval_nat_ladder_c00449 n (by omega) (by omega)
          · -- n <= 28709309903
            rcases Nat.lt_or_ge 28644891889 n with h12 | h12
            · -- n > 28644891889
              exact RamareSaouter2003.prime_interval_nat_ladder_c00448 n (by omega) (by omega)
            · -- n <= 28644891889
              exact RamareSaouter2003.prime_interval_nat_ladder_c00447 n (by omega) (by omega)
        · -- n <= 28580624767
          rcases Nat.lt_or_ge 28452541727 n with h10 | h10
          · -- n > 28452541727
            rcases Nat.lt_or_ge 28516508221 n with h12 | h12
            · -- n > 28516508221
              exact RamareSaouter2003.prime_interval_nat_ladder_c00446 n (by omega) (by omega)
            · -- n <= 28516508221
              exact RamareSaouter2003.prime_interval_nat_ladder_c00445 n (by omega) (by omega)
          · -- n <= 28452541727
            exact RamareSaouter2003.prime_interval_nat_ladder_c00444 n (by omega) (by omega)
      · -- n <= 28388725091
        rcases Nat.lt_or_ge 28198170139 n with h8 | h8
        · -- n > 28198170139
          rcases Nat.lt_or_ge 28261539637 n with h10 | h10
          · -- n > 28261539637
            rcases Nat.lt_or_ge 28325057801 n with h12 | h12
            · -- n > 28325057801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00443 n (by omega) (by omega)
            · -- n <= 28325057801
              exact RamareSaouter2003.prime_interval_nat_ladder_c00442 n (by omega) (by omega)
          · -- n <= 28261539637
            exact RamareSaouter2003.prime_interval_nat_ladder_c00441 n (by omega) (by omega)
        · -- n <= 28198170139
          rcases Nat.lt_or_ge 28071875731 n with h10 | h10
          · -- n > 28071875731
            rcases Nat.lt_or_ge 28134948943 n with h12 | h12
            · -- n > 28134948943
              exact RamareSaouter2003.prime_interval_nat_ladder_c00440 n (by omega) (by omega)
            · -- n <= 28134948943
              exact RamareSaouter2003.prime_interval_nat_ladder_c00439 n (by omega) (by omega)
          · -- n <= 28071875731
            exact RamareSaouter2003.prime_interval_nat_ladder_c00438 n (by omega) (by omega)
    · -- n <= 28008950069
      rcases Nat.lt_or_ge 27634475929 n with h6 | h6
      · -- n > 27634475929
        rcases Nat.lt_or_ge 27821055239 n with h8 | h8
        · -- n > 27821055239
          rcases Nat.lt_or_ge 27883540183 n with h10 | h10
          · -- n > 27883540183
            rcases Nat.lt_or_ge 27946171699 n with h12 | h12
            · -- n > 27946171699
              exact RamareSaouter2003.prime_interval_nat_ladder_c00437 n (by omega) (by omega)
            · -- n <= 27946171699
              exact RamareSaouter2003.prime_interval_nat_ladder_c00436 n (by omega) (by omega)
          · -- n <= 27883540183
            exact RamareSaouter2003.prime_interval_nat_ladder_c00435 n (by omega) (by omega)
        · -- n <= 27821055239
          rcases Nat.lt_or_ge 27696523441 n with h10 | h10
          · -- n > 27696523441
            rcases Nat.lt_or_ge 27758716411 n with h12 | h12
            · -- n > 27758716411
              exact RamareSaouter2003.prime_interval_nat_ladder_c00434 n (by omega) (by omega)
            · -- n <= 27758716411
              exact RamareSaouter2003.prime_interval_nat_ladder_c00433 n (by omega) (by omega)
          · -- n <= 27696523441
            exact RamareSaouter2003.prime_interval_nat_ladder_c00432 n (by omega) (by omega)
      · -- n <= 27634475929
        rcases Nat.lt_or_ge 27449202601 n with h8 | h8
        · -- n > 27449202601
          rcases Nat.lt_or_ge 27510815833 n with h10 | h10
          · -- n > 27510815833
            rcases Nat.lt_or_ge 27572573503 n with h12 | h12
            · -- n > 27572573503
              exact RamareSaouter2003.prime_interval_nat_ladder_c00431 n (by omega) (by omega)
            · -- n <= 27572573503
              exact RamareSaouter2003.prime_interval_nat_ladder_c00430 n (by omega) (by omega)
          · -- n <= 27510815833
            exact RamareSaouter2003.prime_interval_nat_ladder_c00429 n (by omega) (by omega)
        · -- n <= 27449202601
          rcases Nat.lt_or_ge 27326408017 n with h10 | h10
          · -- n > 27326408017
            rcases Nat.lt_or_ge 27387733423 n with h12 | h12
            · -- n > 27387733423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00428 n (by omega) (by omega)
            · -- n <= 27387733423
              exact RamareSaouter2003.prime_interval_nat_ladder_c00427 n (by omega) (by omega)
          · -- n <= 27326408017
            exact RamareSaouter2003.prime_interval_nat_ladder_c00426 n (by omega) (by omega)
  · -- n <= 27265225847
    rcases Nat.lt_or_ge 26482745717 n with h4 | h4
    · -- n > 26482745717
      rcases Nat.lt_or_ge 26840935621 n with h6 | h6
      · -- n > 26840935621
        rcases Nat.lt_or_ge 27021923821 n with h8 | h8
        · -- n > 27021923821
          rcases Nat.lt_or_ge 27143290249 n with h10 | h10
          · -- n > 27143290249
            rcases Nat.lt_or_ge 27204186707 n with h12 | h12
            · -- n > 27204186707
              exact RamareSaouter2003.prime_interval_nat_ladder_c00425 n (by omega) (by omega)
            · -- n <= 27204186707
              exact RamareSaouter2003.prime_interval_nat_ladder_c00424 n (by omega) (by omega)
          · -- n <= 27143290249
            rcases Nat.lt_or_ge 27082536049 n with h12 | h12
            · -- n > 27082536049
              exact RamareSaouter2003.prime_interval_nat_ladder_c00423 n (by omega) (by omega)
            · -- n <= 27082536049
              exact RamareSaouter2003.prime_interval_nat_ladder_c00422 n (by omega) (by omega)
        · -- n <= 27021923821
          rcases Nat.lt_or_ge 26901124039 n with h10 | h10
          · -- n > 26901124039
            rcases Nat.lt_or_ge 26961453223 n with h12 | h12
            · -- n > 26961453223
              exact RamareSaouter2003.prime_interval_nat_ladder_c00421 n (by omega) (by omega)
            · -- n <= 26961453223
              exact RamareSaouter2003.prime_interval_nat_ladder_c00420 n (by omega) (by omega)
          · -- n <= 26901124039
            exact RamareSaouter2003.prime_interval_nat_ladder_c00419 n (by omega) (by omega)
      · -- n <= 26840935621
        rcases Nat.lt_or_ge 26661212551 n with h8 | h8
        · -- n > 26661212551
          rcases Nat.lt_or_ge 26720980217 n with h10 | h10
          · -- n > 26720980217
            rcases Nat.lt_or_ge 26780887799 n with h12 | h12
            · -- n > 26780887799
              exact RamareSaouter2003.prime_interval_nat_ladder_c00418 n (by omega) (by omega)
            · -- n <= 26780887799
              exact RamareSaouter2003.prime_interval_nat_ladder_c00417 n (by omega) (by omega)
          · -- n <= 26720980217
            exact RamareSaouter2003.prime_interval_nat_ladder_c00416 n (by omega) (by omega)
        · -- n <= 26661212551
          rcases Nat.lt_or_ge 26542095689 n with h10 | h10
          · -- n > 26542095689
            rcases Nat.lt_or_ge 26601584557 n with h12 | h12
            · -- n > 26601584557
              exact RamareSaouter2003.prime_interval_nat_ladder_c00415 n (by omega) (by omega)
            · -- n <= 26601584557
              exact RamareSaouter2003.prime_interval_nat_ladder_c00414 n (by omega) (by omega)
          · -- n <= 26542095689
            exact RamareSaouter2003.prime_interval_nat_ladder_c00413 n (by omega) (by omega)
    · -- n <= 26482745717
      rcases Nat.lt_or_ge 26129543749 n with h6 | h6
      · -- n > 26129543749
        rcases Nat.lt_or_ge 26305525723 n with h8 | h8
        · -- n > 26305525723
          rcases Nat.lt_or_ge 26364461059 n with h10 | h10
          · -- n > 26364461059
            rcases Nat.lt_or_ge 26423534287 n with h12 | h12
            · -- n > 26423534287
              exact RamareSaouter2003.prime_interval_nat_ladder_c00412 n (by omega) (by omega)
            · -- n <= 26423534287
              exact RamareSaouter2003.prime_interval_nat_ladder_c00411 n (by omega) (by omega)
          · -- n <= 26364461059
            exact RamareSaouter2003.prime_interval_nat_ladder_c00410 n (by omega) (by omega)
        · -- n <= 26305525723
          rcases Nat.lt_or_ge 26188067453 n with h10 | h10
          · -- n > 26188067453
            rcases Nat.lt_or_ge 26246728033 n with h12 | h12
            · -- n > 26246728033
              exact RamareSaouter2003.prime_interval_nat_ladder_c00409 n (by omega) (by omega)
            · -- n <= 26246728033
              exact RamareSaouter2003.prime_interval_nat_ladder_c00408 n (by omega) (by omega)
          · -- n <= 26188067453
            exact RamareSaouter2003.prime_interval_nat_ladder_c00407 n (by omega) (by omega)
      · -- n <= 26129543749
        rcases Nat.lt_or_ge 25954790731 n with h8 | h8
        · -- n > 25954790731
          rcases Nat.lt_or_ge 26012905753 n with h10 | h10
          · -- n > 26012905753
            rcases Nat.lt_or_ge 26071156637 n with h12 | h12
            · -- n > 26071156637
              exact RamareSaouter2003.prime_interval_nat_ladder_c00406 n (by omega) (by omega)
            · -- n <= 26071156637
              exact RamareSaouter2003.prime_interval_nat_ladder_c00405 n (by omega) (by omega)
          · -- n <= 26012905753
            exact RamareSaouter2003.prime_interval_nat_ladder_c00404 n (by omega) (by omega)
        · -- n <= 25954790731
          rcases Nat.lt_or_ge 25838966957 n with h10 | h10
          · -- n > 25838966957
            rcases Nat.lt_or_ge 25896811253 n with h12 | h12
            · -- n > 25896811253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00403 n (by omega) (by omega)
            · -- n <= 25896811253
              exact RamareSaouter2003.prime_interval_nat_ladder_c00402 n (by omega) (by omega)
          · -- n <= 25838966957
            exact RamareSaouter2003.prime_interval_nat_ladder_c00401 n (by omega) (by omega)
