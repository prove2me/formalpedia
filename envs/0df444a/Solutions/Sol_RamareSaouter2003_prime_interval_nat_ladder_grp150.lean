-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp150
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T07:24:22.792691+00:00
-- url     : https://prove2.me/submissions/3c9efd21-0bb8-4de4-b66d-f6b0bf6a24d1

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07450
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07492

theorem solution (n : Nat)
    (hn : 3108818837989423529 < n) (hupper : n <= 3570765072310602017) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3327088744744848143 n with h2 | h2
  · -- n > 3327088744744848143
    rcases Nat.lt_or_ge 3441905279094360241 n with h4 | h4
    · -- n > 3441905279094360241
      rcases Nat.lt_or_ge 3500790984097496429 n with h6 | h6
      · -- n > 3500790984097496429
        rcases Nat.lt_or_ge 3530610270033598417 n with h8 | h8
        · -- n > 3530610270033598417
          rcases Nat.lt_or_ge 3550630941490968029 n with h10 | h10
          · -- n > 3550630941490968029
            rcases Nat.lt_or_ge 3560683684713777679 n with h12 | h12
            · -- n > 3560683684713777679
              exact RamareSaouter2003.prime_interval_nat_ladder_c07492 n (by omega) (by omega)
            · -- n <= 3560683684713777679
              exact RamareSaouter2003.prime_interval_nat_ladder_c07491 n (by omega) (by omega)
          · -- n <= 3550630941490968029
            rcases Nat.lt_or_ge 3540606430876078387 n with h12 | h12
            · -- n > 3540606430876078387
              exact RamareSaouter2003.prime_interval_nat_ladder_c07490 n (by omega) (by omega)
            · -- n <= 3540606430876078387
              exact RamareSaouter2003.prime_interval_nat_ladder_c07489 n (by omega) (by omega)
        · -- n <= 3530610270033598417
          rcases Nat.lt_or_ge 3510702747305632261 n with h10 | h10
          · -- n > 3510702747305632261
            rcases Nat.lt_or_ge 3520642271649578213 n with h12 | h12
            · -- n > 3520642271649578213
              exact RamareSaouter2003.prime_interval_nat_ladder_c07488 n (by omega) (by omega)
            · -- n <= 3520642271649578213
              exact RamareSaouter2003.prime_interval_nat_ladder_c07487 n (by omega) (by omega)
          · -- n <= 3510702747305632261
            exact RamareSaouter2003.prime_interval_nat_ladder_c07486 n (by omega) (by omega)
      · -- n <= 3500790984097496429
        rcases Nat.lt_or_ge 3471223258307372699 n with h8 | h8
        · -- n > 3471223258307372699
          rcases Nat.lt_or_ge 3481051337947980289 n with h10 | h10
          · -- n > 3481051337947980289
            rcases Nat.lt_or_ge 3490907238020291261 n with h12 | h12
            · -- n > 3490907238020291261
              exact RamareSaouter2003.prime_interval_nat_ladder_c07485 n (by omega) (by omega)
            · -- n <= 3490907238020291261
              exact RamareSaouter2003.prime_interval_nat_ladder_c07484 n (by omega) (by omega)
          · -- n <= 3481051337947980289
            exact RamareSaouter2003.prime_interval_nat_ladder_c07483 n (by omega) (by omega)
        · -- n <= 3471223258307372699
          rcases Nat.lt_or_ge 3451650324672763237 n with h10 | h10
          · -- n > 3451650324672763237
            rcases Nat.lt_or_ge 3461422906665533807 n with h12 | h12
            · -- n > 3461422906665533807
              exact RamareSaouter2003.prime_interval_nat_ladder_c07482 n (by omega) (by omega)
            · -- n <= 3461422906665533807
              exact RamareSaouter2003.prime_interval_nat_ladder_c07481 n (by omega) (by omega)
          · -- n <= 3451650324672763237
            exact RamareSaouter2003.prime_interval_nat_ladder_c07480 n (by omega) (by omega)
    · -- n <= 3441905279094360241
      rcases Nat.lt_or_ge 3384010020838215361 n with h6 | h6
      · -- n > 3384010020838215361
        rcases Nat.lt_or_ge 3412834954565117989 n with h8 | h8
        · -- n > 3412834954565117989
          rcases Nat.lt_or_ge 3422497641069628237 n with h10 | h10
          · -- n > 3422497641069628237
            rcases Nat.lt_or_ge 3432187737228080903 n with h12 | h12
            · -- n > 3432187737228080903
              exact RamareSaouter2003.prime_interval_nat_ladder_c07479 n (by omega) (by omega)
            · -- n <= 3432187737228080903
              exact RamareSaouter2003.prime_interval_nat_ladder_c07478 n (by omega) (by omega)
          · -- n <= 3422497641069628237
            exact RamareSaouter2003.prime_interval_nat_ladder_c07477 n (by omega) (by omega)
        · -- n <= 3412834954565117989
          rcases Nat.lt_or_ge 3393591187338829937 n with h10 | h10
          · -- n > 3393591187338829937
            rcases Nat.lt_or_ge 3403199460927645037 n with h12 | h12
            · -- n > 3403199460927645037
              exact RamareSaouter2003.prime_interval_nat_ladder_c07476 n (by omega) (by omega)
            · -- n <= 3403199460927645037
              exact RamareSaouter2003.prime_interval_nat_ladder_c07475 n (by omega) (by omega)
          · -- n <= 3393591187338829937
            exact RamareSaouter2003.prime_interval_nat_ladder_c07474 n (by omega) (by omega)
      · -- n <= 3384010020838215361
        rcases Nat.lt_or_ge 3355428569617496347 n with h8 | h8
        · -- n > 3355428569617496347
          rcases Nat.lt_or_ge 3364928773211284507 n with h10 | h10
          · -- n > 3364928773211284507
            rcases Nat.lt_or_ge 3374455919260895789 n with h12 | h12
            · -- n > 3374455919260895789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07473 n (by omega) (by omega)
            · -- n <= 3374455919260895789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07472 n (by omega) (by omega)
          · -- n <= 3364928773211284507
            exact RamareSaouter2003.prime_interval_nat_ladder_c07471 n (by omega) (by omega)
        · -- n <= 3355428569617496347
          rcases Nat.lt_or_ge 3336508630774849471 n with h10 | h10
          · -- n > 3336508630774849471
            rcases Nat.lt_or_ge 3345955295656499297 n with h12 | h12
            · -- n > 3345955295656499297
              exact RamareSaouter2003.prime_interval_nat_ladder_c07470 n (by omega) (by omega)
            · -- n <= 3345955295656499297
              exact RamareSaouter2003.prime_interval_nat_ladder_c07469 n (by omega) (by omega)
          · -- n <= 3336508630774849471
            exact RamareSaouter2003.prime_interval_nat_ladder_c07468 n (by omega) (by omega)
  · -- n <= 3327088744744848143
    rcases Nat.lt_or_ge 3216102348442054481 n with h4 | h4
    · -- n > 3216102348442054481
      rcases Nat.lt_or_ge 3271124877575100319 n with h6 | h6
      · -- n > 3271124877575100319
        rcases Nat.lt_or_ge 3298988052324513943 n with h8 | h8
        · -- n > 3298988052324513943
          rcases Nat.lt_or_ge 3308328460687660141 n with h10 | h10
          · -- n > 3308328460687660141
            rcases Nat.lt_or_ge 3317695348070404487 n with h12 | h12
            · -- n > 3317695348070404487
              exact RamareSaouter2003.prime_interval_nat_ladder_c07467 n (by omega) (by omega)
            · -- n <= 3317695348070404487
              exact RamareSaouter2003.prime_interval_nat_ladder_c07466 n (by omega) (by omega)
          · -- n <= 3308328460687660141
            exact RamareSaouter2003.prime_interval_nat_ladder_c07465 n (by omega) (by omega)
        · -- n <= 3298988052324513943
          rcases Nat.lt_or_ge 3280386261763660051 n with h10 | h10
          · -- n > 3280386261763660051
            rcases Nat.lt_or_ge 3289674022883855119 n with h12 | h12
            · -- n > 3289674022883855119
              exact RamareSaouter2003.prime_interval_nat_ladder_c07464 n (by omega) (by omega)
            · -- n <= 3289674022883855119
              exact RamareSaouter2003.prime_interval_nat_ladder_c07463 n (by omega) (by omega)
          · -- n <= 3280386261763660051
            exact RamareSaouter2003.prime_interval_nat_ladder_c07462 n (by omega) (by omega)
      · -- n <= 3271124877575100319
        rcases Nat.lt_or_ge 3243497045650888891 n with h8 | h8
        · -- n > 3243497045650888891
          rcases Nat.lt_or_ge 3252680383926929441 n with h10 | h10
          · -- n > 3252680383926929441
            rcases Nat.lt_or_ge 3261889649874580997 n with h12 | h12
            · -- n > 3261889649874580997
              exact RamareSaouter2003.prime_interval_nat_ladder_c07461 n (by omega) (by omega)
            · -- n <= 3261889649874580997
              exact RamareSaouter2003.prime_interval_nat_ladder_c07460 n (by omega) (by omega)
          · -- n <= 3252680383926929441
            exact RamareSaouter2003.prime_interval_nat_ladder_c07459 n (by omega) (by omega)
        · -- n <= 3243497045650888891
          rcases Nat.lt_or_ge 3225208116952232407 n with h10 | h10
          · -- n > 3225208116952232407
            rcases Nat.lt_or_ge 3234339659575040711 n with h12 | h12
            · -- n > 3234339659575040711
              exact RamareSaouter2003.prime_interval_nat_ladder_c07458 n (by omega) (by omega)
            · -- n <= 3234339659575040711
              exact RamareSaouter2003.prime_interval_nat_ladder_c07457 n (by omega) (by omega)
          · -- n <= 3225208116952232407
            exact RamareSaouter2003.prime_interval_nat_ladder_c07456 n (by omega) (by omega)
    · -- n <= 3216102348442054481
      rcases Nat.lt_or_ge 3162005533667081267 n with h6 | h6
      · -- n > 3162005533667081267
        rcases Nat.lt_or_ge 3188939293567667527 n with h8 | h8
        · -- n > 3188939293567667527
          rcases Nat.lt_or_ge 3197968052326873481 n with h10 | h10
          · -- n > 3197968052326873481
            rcases Nat.lt_or_ge 3207022328477248069 n with h12 | h12
            · -- n > 3207022328477248069
              exact RamareSaouter2003.prime_interval_nat_ladder_c07455 n (by omega) (by omega)
            · -- n <= 3207022328477248069
              exact RamareSaouter2003.prime_interval_nat_ladder_c07454 n (by omega) (by omega)
          · -- n <= 3197968052326873481
            exact RamareSaouter2003.prime_interval_nat_ladder_c07453 n (by omega) (by omega)
        · -- n <= 3188939293567667527
          rcases Nat.lt_or_ge 3170958102111509419 n with h10 | h10
          · -- n > 3170958102111509419
            rcases Nat.lt_or_ge 3179935927166963707 n with h12 | h12
            · -- n > 3179935927166963707
              exact RamareSaouter2003.prime_interval_nat_ladder_c07452 n (by omega) (by omega)
            · -- n <= 3179935927166963707
              exact RamareSaouter2003.prime_interval_nat_ladder_c07451 n (by omega) (by omega)
          · -- n <= 3170958102111509419
            exact RamareSaouter2003.prime_interval_nat_ladder_c07450 n (by omega) (by omega)
      · -- n <= 3162005533667081267
        rcases Nat.lt_or_ge 3135299426455452439 n with h8 | h8
        · -- n > 3135299426455452439
          rcases Nat.lt_or_ge 3144176355794867413 n with h10 | h10
          · -- n > 3144176355794867413
            rcases Nat.lt_or_ge 3153078380731191659 n with h12 | h12
            · -- n > 3153078380731191659
              exact RamareSaouter2003.prime_interval_nat_ladder_c07449 n (by omega) (by omega)
            · -- n <= 3153078380731191659
              exact RamareSaouter2003.prime_interval_nat_ladder_c07448 n (by omega) (by omega)
          · -- n <= 3144176355794867413
            exact RamareSaouter2003.prime_interval_nat_ladder_c07447 n (by omega) (by omega)
        · -- n <= 3135299426455452439
          rcases Nat.lt_or_ge 3117620812467359521 n with h10 | h10
          · -- n > 3117620812467359521
            rcases Nat.lt_or_ge 3126447674233817449 n with h12 | h12
            · -- n > 3126447674233817449
              exact RamareSaouter2003.prime_interval_nat_ladder_c07446 n (by omega) (by omega)
            · -- n <= 3126447674233817449
              exact RamareSaouter2003.prime_interval_nat_ladder_c07445 n (by omega) (by omega)
          · -- n <= 3117620812467359521
            exact RamareSaouter2003.prime_interval_nat_ladder_c07444 n (by omega) (by omega)
