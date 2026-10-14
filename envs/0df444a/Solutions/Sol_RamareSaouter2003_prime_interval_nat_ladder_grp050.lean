-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp050
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T22:05:35.130053+00:00
-- url     : https://prove2.me/submissions/22607da8-84f9-463f-9291-b6c5a71c123b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02451
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02452
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02453
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02454
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02455
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02456
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02457
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02458
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02459
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02460
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02461
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02462
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02463
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02464
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02465
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02466
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02467
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02468
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02469
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02470
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02471
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02472
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02473
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02474
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02475
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02476
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02477
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02478
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02479
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02480
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02481
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02482
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02483
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02484
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02485
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02486
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02487
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02488
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02489
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02490
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02491
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02492
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02500

theorem solution (n : Nat)
    (hn : 3896894525047 < n) (hupper : n <= 4409511496801) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 4145286626189 n with h2 | h2
  · -- n > 4145286626189
    rcases Nat.lt_or_ge 4270077958969 n with h4 | h4
    · -- n > 4270077958969
      rcases Nat.lt_or_ge 4333875423043 n with h6 | h6
      · -- n > 4333875423043
        rcases Nat.lt_or_ge 4366130709401 n with h8 | h8
        · -- n > 4366130709401
          rcases Nat.lt_or_ge 4387767491531 n with h10 | h10
          · -- n > 4387767491531
            rcases Nat.lt_or_ge 4398626058109 n with h12 | h12
            · -- n > 4398626058109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02500 n (by omega) (by omega)
            · -- n <= 4398626058109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02499 n (by omega) (by omega)
          · -- n <= 4387767491531
            rcases Nat.lt_or_ge 4376935730413 n with h12 | h12
            · -- n > 4376935730413
              exact RamareSaouter2003.prime_interval_nat_ladder_c02498 n (by omega) (by omega)
            · -- n <= 4376935730413
              exact RamareSaouter2003.prime_interval_nat_ladder_c02497 n (by omega) (by omega)
        · -- n <= 4366130709401
          rcases Nat.lt_or_ge 4344600621241 n with h10 | h10
          · -- n > 4344600621241
            rcases Nat.lt_or_ge 4355352361447 n with h12 | h12
            · -- n > 4355352361447
              exact RamareSaouter2003.prime_interval_nat_ladder_c02496 n (by omega) (by omega)
            · -- n <= 4355352361447
              exact RamareSaouter2003.prime_interval_nat_ladder_c02495 n (by omega) (by omega)
          · -- n <= 4344600621241
            exact RamareSaouter2003.prime_interval_nat_ladder_c02494 n (by omega) (by omega)
      · -- n <= 4333875423043
        rcases Nat.lt_or_ge 4301858426573 n with h8 | h8
        · -- n > 4301858426573
          rcases Nat.lt_or_ge 4312504391093 n with h10 | h10
          · -- n > 4312504391093
            rcases Nat.lt_or_ge 4323176701589 n with h12 | h12
            · -- n > 4323176701589
              exact RamareSaouter2003.prime_interval_nat_ladder_c02493 n (by omega) (by omega)
            · -- n <= 4323176701589
              exact RamareSaouter2003.prime_interval_nat_ladder_c02492 n (by omega) (by omega)
          · -- n <= 4312504391093
            exact RamareSaouter2003.prime_interval_nat_ladder_c02491 n (by omega) (by omega)
        · -- n <= 4301858426573
          rcases Nat.lt_or_ge 4280645275237 n with h10 | h10
          · -- n > 4280645275237
            rcases Nat.lt_or_ge 4291238742881 n with h12 | h12
            · -- n > 4291238742881
              exact RamareSaouter2003.prime_interval_nat_ladder_c02490 n (by omega) (by omega)
            · -- n <= 4291238742881
              exact RamareSaouter2003.prime_interval_nat_ladder_c02489 n (by omega) (by omega)
          · -- n <= 4280645275237
            exact RamareSaouter2003.prime_interval_nat_ladder_c02488 n (by omega) (by omega)
    · -- n <= 4270077958969
      rcases Nat.lt_or_ge 4207219634993 n with h6 | h6
      · -- n > 4207219634993
        rcases Nat.lt_or_ge 4238532273389 n with h8 | h8
        · -- n > 4238532273389
          rcases Nat.lt_or_ge 4249021522363 n with h10 | h10
          · -- n > 4249021522363
            rcases Nat.lt_or_ge 4259536729457 n with h12 | h12
            · -- n > 4259536729457
              exact RamareSaouter2003.prime_interval_nat_ladder_c02487 n (by omega) (by omega)
            · -- n <= 4259536729457
              exact RamareSaouter2003.prime_interval_nat_ladder_c02486 n (by omega) (by omega)
          · -- n <= 4249021522363
            exact RamareSaouter2003.prime_interval_nat_ladder_c02485 n (by omega) (by omega)
        · -- n <= 4238532273389
          rcases Nat.lt_or_ge 4217631393553 n with h10 | h10
          · -- n > 4217631393553
            rcases Nat.lt_or_ge 4228068918401 n with h12 | h12
            · -- n > 4228068918401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02484 n (by omega) (by omega)
            · -- n <= 4228068918401
              exact RamareSaouter2003.prime_interval_nat_ladder_c02483 n (by omega) (by omega)
          · -- n <= 4217631393553
            exact RamareSaouter2003.prime_interval_nat_ladder_c02482 n (by omega) (by omega)
      · -- n <= 4207219634993
        rcases Nat.lt_or_ge 4176138322243 n with h8 | h8
        · -- n > 4176138322243
          rcases Nat.lt_or_ge 4186473162743 n with h10 | h10
          · -- n > 4186473162743
            rcases Nat.lt_or_ge 4196833579193 n with h12 | h12
            · -- n > 4196833579193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02481 n (by omega) (by omega)
            · -- n <= 4196833579193
              exact RamareSaouter2003.prime_interval_nat_ladder_c02480 n (by omega) (by omega)
          · -- n <= 4186473162743
            exact RamareSaouter2003.prime_interval_nat_ladder_c02479 n (by omega) (by omega)
        · -- n <= 4176138322243
          rcases Nat.lt_or_ge 4155545116883 n with h10 | h10
          · -- n > 4155545116883
            rcases Nat.lt_or_ge 4165828994629 n with h12 | h12
            · -- n > 4165828994629
              exact RamareSaouter2003.prime_interval_nat_ladder_c02478 n (by omega) (by omega)
            · -- n <= 4165828994629
              exact RamareSaouter2003.prime_interval_nat_ladder_c02477 n (by omega) (by omega)
          · -- n <= 4155545116883
            exact RamareSaouter2003.prime_interval_nat_ladder_c02476 n (by omega) (by omega)
  · -- n <= 4145286626189
    rcases Nat.lt_or_ge 4014208164859 n with h4 | h4
    · -- n > 4014208164859
      rcases Nat.lt_or_ge 4074182784601 n with h6 | h6
      · -- n > 4074182784601
        rcases Nat.lt_or_ge 4104505283479 n with h8 | h8
        · -- n > 4104505283479
          rcases Nat.lt_or_ge 4124845555703 n with h10 | h10
          · -- n > 4124845555703
            rcases Nat.lt_or_ge 4135053459983 n with h12 | h12
            · -- n > 4135053459983
              exact RamareSaouter2003.prime_interval_nat_ladder_c02475 n (by omega) (by omega)
            · -- n <= 4135053459983
              exact RamareSaouter2003.prime_interval_nat_ladder_c02474 n (by omega) (by omega)
          · -- n <= 4124845555703
            rcases Nat.lt_or_ge 4114662851099 n with h12 | h12
            · -- n > 4114662851099
              exact RamareSaouter2003.prime_interval_nat_ladder_c02473 n (by omega) (by omega)
            · -- n <= 4114662851099
              exact RamareSaouter2003.prime_interval_nat_ladder_c02472 n (by omega) (by omega)
        · -- n <= 4104505283479
          rcases Nat.lt_or_ge 4084265312051 n with h10 | h10
          · -- n > 4084265312051
            rcases Nat.lt_or_ge 4094372791109 n with h12 | h12
            · -- n > 4094372791109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02471 n (by omega) (by omega)
            · -- n <= 4094372791109
              exact RamareSaouter2003.prime_interval_nat_ladder_c02470 n (by omega) (by omega)
          · -- n <= 4084265312051
            exact RamareSaouter2003.prime_interval_nat_ladder_c02469 n (by omega) (by omega)
      · -- n <= 4074182784601
        rcases Nat.lt_or_ge 4044084296677 n with h8 | h8
        · -- n > 4044084296677
          rcases Nat.lt_or_ge 4054092338299 n with h10 | h10
          · -- n > 4054092338299
            rcases Nat.lt_or_ge 4064125147157 n with h12 | h12
            · -- n > 4064125147157
              exact RamareSaouter2003.prime_interval_nat_ladder_c02468 n (by omega) (by omega)
            · -- n <= 4064125147157
              exact RamareSaouter2003.prime_interval_nat_ladder_c02467 n (by omega) (by omega)
          · -- n <= 4054092338299
            exact RamareSaouter2003.prime_interval_nat_ladder_c02466 n (by omega) (by omega)
        · -- n <= 4044084296677
          rcases Nat.lt_or_ge 4024142270963 n with h10 | h10
          · -- n > 4024142270963
            rcases Nat.lt_or_ge 4034100961183 n with h12 | h12
            · -- n > 4034100961183
              exact RamareSaouter2003.prime_interval_nat_ladder_c02465 n (by omega) (by omega)
            · -- n <= 4034100961183
              exact RamareSaouter2003.prime_interval_nat_ladder_c02464 n (by omega) (by omega)
          · -- n <= 4024142270963
            exact RamareSaouter2003.prime_interval_nat_ladder_c02463 n (by omega) (by omega)
    · -- n <= 4014208164859
      rcases Nat.lt_or_ge 3955116410473 n with h6 | h6
      · -- n > 3955116410473
        rcases Nat.lt_or_ge 3984552746287 n with h8 | h8
        · -- n > 3984552746287
          rcases Nat.lt_or_ge 3994413462967 n with h10 | h10
          · -- n > 3994413462967
            rcases Nat.lt_or_ge 4004298582377 n with h12 | h12
            · -- n > 4004298582377
              exact RamareSaouter2003.prime_interval_nat_ladder_c02462 n (by omega) (by omega)
            · -- n <= 4004298582377
              exact RamareSaouter2003.prime_interval_nat_ladder_c02461 n (by omega) (by omega)
          · -- n <= 3994413462967
            exact RamareSaouter2003.prime_interval_nat_ladder_c02460 n (by omega) (by omega)
        · -- n <= 3984552746287
          rcases Nat.lt_or_ge 3964904280059 n with h10 | h10
          · -- n > 3964904280059
            rcases Nat.lt_or_ge 3974716371973 n with h12 | h12
            · -- n > 3974716371973
              exact RamareSaouter2003.prime_interval_nat_ladder_c02459 n (by omega) (by omega)
            · -- n <= 3974716371973
              exact RamareSaouter2003.prime_interval_nat_ladder_c02458 n (by omega) (by omega)
          · -- n <= 3964904280059
            exact RamareSaouter2003.prime_interval_nat_ladder_c02457 n (by omega) (by omega)
      · -- n <= 3955116410473
        rcases Nat.lt_or_ge 3925897538917 n with h8 | h8
        · -- n > 3925897538917
          rcases Nat.lt_or_ge 3935613099511 n with h10 | h10
          · -- n > 3935613099511
            rcases Nat.lt_or_ge 3945352703563 n with h12 | h12
            · -- n > 3945352703563
              exact RamareSaouter2003.prime_interval_nat_ladder_c02456 n (by omega) (by omega)
            · -- n <= 3945352703563
              exact RamareSaouter2003.prime_interval_nat_ladder_c02455 n (by omega) (by omega)
          · -- n <= 3935613099511
            exact RamareSaouter2003.prime_interval_nat_ladder_c02454 n (by omega) (by omega)
        · -- n <= 3925897538917
          rcases Nat.lt_or_ge 3906538310821 n with h10 | h10
          · -- n > 3906538310821
            rcases Nat.lt_or_ge 3916205962439 n with h12 | h12
            · -- n > 3916205962439
              exact RamareSaouter2003.prime_interval_nat_ladder_c02453 n (by omega) (by omega)
            · -- n <= 3916205962439
              exact RamareSaouter2003.prime_interval_nat_ladder_c02452 n (by omega) (by omega)
          · -- n <= 3906538310821
            exact RamareSaouter2003.prime_interval_nat_ladder_c02451 n (by omega) (by omega)
