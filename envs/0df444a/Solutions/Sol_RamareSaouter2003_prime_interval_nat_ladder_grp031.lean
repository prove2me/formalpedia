-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T08:38:28.396167+00:00
-- url     : https://prove2.me/submissions/38b8c0be-1eb1-4e25-8d9e-9c3cd26eec62

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c01550

theorem solution (n : Nat)
    (hn : 354000949151 < n) (hupper : n <= 401493320309) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 376993121363 n with h2 | h2
  · -- n > 376993121363
    rcases Nat.lt_or_ge 388559017657 n with h4 | h4
    · -- n > 388559017657
      rcases Nat.lt_or_ge 394475603887 n with h6 | h6
      · -- n > 394475603887
        rcases Nat.lt_or_ge 397467910501 n with h8 | h8
        · -- n > 397467910501
          rcases Nat.lt_or_ge 399475498273 n with h10 | h10
          · -- n > 399475498273
            rcases Nat.lt_or_ge 400483126669 n with h12 | h12
            · -- n > 400483126669
              exact RamareSaouter2003.prime_interval_nat_ladder_c01550 n (by omega) (by omega)
            · -- n <= 400483126669
              exact RamareSaouter2003.prime_interval_nat_ladder_c01549 n (by omega) (by omega)
          · -- n <= 399475498273
            rcases Nat.lt_or_ge 398470428361 n with h12 | h12
            · -- n > 398470428361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01548 n (by omega) (by omega)
            · -- n <= 398470428361
              exact RamareSaouter2003.prime_interval_nat_ladder_c01547 n (by omega) (by omega)
        · -- n <= 397467910501
          rcases Nat.lt_or_ge 395470504861 n with h10 | h10
          · -- n > 395470504861
            rcases Nat.lt_or_ge 396467938147 n with h12 | h12
            · -- n > 396467938147
              exact RamareSaouter2003.prime_interval_nat_ladder_c01546 n (by omega) (by omega)
            · -- n <= 396467938147
              exact RamareSaouter2003.prime_interval_nat_ladder_c01545 n (by omega) (by omega)
          · -- n <= 395470504861
            exact RamareSaouter2003.prime_interval_nat_ladder_c01544 n (by omega) (by omega)
      · -- n <= 394475603887
        rcases Nat.lt_or_ge 391506030977 n with h8 | h8
        · -- n > 391506030977
          rcases Nat.lt_or_ge 392493373423 n with h10 | h10
          · -- n > 392493373423
            rcases Nat.lt_or_ge 393483228893 n with h12 | h12
            · -- n > 393483228893
              exact RamareSaouter2003.prime_interval_nat_ladder_c01543 n (by omega) (by omega)
            · -- n <= 393483228893
              exact RamareSaouter2003.prime_interval_nat_ladder_c01542 n (by omega) (by omega)
          · -- n <= 392493373423
            exact RamareSaouter2003.prime_interval_nat_ladder_c01541 n (by omega) (by omega)
        · -- n <= 391506030977
          rcases Nat.lt_or_ge 389538859561 n with h10 | h10
          · -- n > 389538859561
            rcases Nat.lt_or_ge 390521195209 n with h12 | h12
            · -- n > 390521195209
              exact RamareSaouter2003.prime_interval_nat_ladder_c01540 n (by omega) (by omega)
            · -- n <= 390521195209
              exact RamareSaouter2003.prime_interval_nat_ladder_c01539 n (by omega) (by omega)
          · -- n <= 389538859561
            exact RamareSaouter2003.prime_interval_nat_ladder_c01538 n (by omega) (by omega)
    · -- n <= 388559017657
      rcases Nat.lt_or_ge 382731979271 n with h6 | h6
      · -- n > 382731979271
        rcases Nat.lt_or_ge 385634390887 n with h8 | h8
        · -- n > 385634390887
          rcases Nat.lt_or_ge 386606789689 n with h10 | h10
          · -- n > 386606789689
            rcases Nat.lt_or_ge 387581663159 n with h12 | h12
            · -- n > 387581663159
              exact RamareSaouter2003.prime_interval_nat_ladder_c01537 n (by omega) (by omega)
            · -- n <= 387581663159
              exact RamareSaouter2003.prime_interval_nat_ladder_c01536 n (by omega) (by omega)
          · -- n <= 386606789689
            exact RamareSaouter2003.prime_interval_nat_ladder_c01535 n (by omega) (by omega)
        · -- n <= 385634390887
          rcases Nat.lt_or_ge 383696992031 n with h10 | h10
          · -- n > 383696992031
            rcases Nat.lt_or_ge 384664460459 n with h12 | h12
            · -- n > 384664460459
              exact RamareSaouter2003.prime_interval_nat_ladder_c01534 n (by omega) (by omega)
            · -- n <= 384664460459
              exact RamareSaouter2003.prime_interval_nat_ladder_c01533 n (by omega) (by omega)
          · -- n <= 383696992031
            exact RamareSaouter2003.prime_interval_nat_ladder_c01532 n (by omega) (by omega)
      · -- n <= 382731979271
        rcases Nat.lt_or_ge 379851612319 n with h8 | h8
        · -- n > 379851612319
          rcases Nat.lt_or_ge 380809295611 n with h10 | h10
          · -- n > 380809295611
            rcases Nat.lt_or_ge 381769415873 n with h12 | h12
            · -- n > 381769415873
              exact RamareSaouter2003.prime_interval_nat_ladder_c01531 n (by omega) (by omega)
            · -- n <= 381769415873
              exact RamareSaouter2003.prime_interval_nat_ladder_c01530 n (by omega) (by omega)
          · -- n <= 380809295611
            exact RamareSaouter2003.prime_interval_nat_ladder_c01529 n (by omega) (by omega)
        · -- n <= 379851612319
          rcases Nat.lt_or_ge 377943531403 n with h10 | h10
          · -- n > 377943531403
            rcases Nat.lt_or_ge 378896359579 n with h12 | h12
            · -- n > 378896359579
              exact RamareSaouter2003.prime_interval_nat_ladder_c01528 n (by omega) (by omega)
            · -- n <= 378896359579
              exact RamareSaouter2003.prime_interval_nat_ladder_c01527 n (by omega) (by omega)
          · -- n <= 377943531403
            exact RamareSaouter2003.prime_interval_nat_ladder_c01526 n (by omega) (by omega)
  · -- n <= 376993121363
    rcases Nat.lt_or_ge 364855050613 n with h4 | h4
    · -- n > 364855050613
      rcases Nat.lt_or_ge 370407442169 n with h6 | h6
      · -- n > 370407442169
        rcases Nat.lt_or_ge 373215539383 n with h8 | h8
        · -- n > 373215539383
          rcases Nat.lt_or_ge 375099531041 n with h10 | h10
          · -- n > 375099531041
            rcases Nat.lt_or_ge 376045123301 n with h12 | h12
            · -- n > 376045123301
              exact RamareSaouter2003.prime_interval_nat_ladder_c01525 n (by omega) (by omega)
            · -- n <= 376045123301
              exact RamareSaouter2003.prime_interval_nat_ladder_c01524 n (by omega) (by omega)
          · -- n <= 375099531041
            rcases Nat.lt_or_ge 374156338429 n with h12 | h12
            · -- n > 374156338429
              exact RamareSaouter2003.prime_interval_nat_ladder_c01523 n (by omega) (by omega)
            · -- n <= 374156338429
              exact RamareSaouter2003.prime_interval_nat_ladder_c01522 n (by omega) (by omega)
        · -- n <= 373215539383
          rcases Nat.lt_or_ge 371341097321 n with h10 | h10
          · -- n > 371341097321
            rcases Nat.lt_or_ge 372277127711 n with h12 | h12
            · -- n > 372277127711
              exact RamareSaouter2003.prime_interval_nat_ladder_c01521 n (by omega) (by omega)
            · -- n <= 372277127711
              exact RamareSaouter2003.prime_interval_nat_ladder_c01520 n (by omega) (by omega)
          · -- n <= 371341097321
            exact RamareSaouter2003.prime_interval_nat_ladder_c01519 n (by omega) (by omega)
      · -- n <= 370407442169
        rcases Nat.lt_or_ge 367620667067 n with h8 | h8
        · -- n > 367620667067
          rcases Nat.lt_or_ge 368547233081 n with h10 | h10
          · -- n > 368547233081
            rcases Nat.lt_or_ge 369476156087 n with h12 | h12
            · -- n > 369476156087
              exact RamareSaouter2003.prime_interval_nat_ladder_c01518 n (by omega) (by omega)
            · -- n <= 369476156087
              exact RamareSaouter2003.prime_interval_nat_ladder_c01517 n (by omega) (by omega)
          · -- n <= 368547233081
            exact RamareSaouter2003.prime_interval_nat_ladder_c01516 n (by omega) (by omega)
        · -- n <= 367620667067
          rcases Nat.lt_or_ge 365774581849 n with h10 | h10
          · -- n > 365774581849
            rcases Nat.lt_or_ge 366696451973 n with h12 | h12
            · -- n > 366696451973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01515 n (by omega) (by omega)
            · -- n <= 366696451973
              exact RamareSaouter2003.prime_interval_nat_ladder_c01514 n (by omega) (by omega)
          · -- n <= 365774581849
            exact RamareSaouter2003.prime_interval_nat_ladder_c01513 n (by omega) (by omega)
    · -- n <= 364855050613
      rcases Nat.lt_or_ge 359386647083 n with h6 | h6
      · -- n > 359386647083
        rcases Nat.lt_or_ge 362110430863 n with h8 | h8
        · -- n > 362110430863
          rcases Nat.lt_or_ge 363022981147 n with h10 | h10
          · -- n > 363022981147
            rcases Nat.lt_or_ge 363937852379 n with h12 | h12
            · -- n > 363937852379
              exact RamareSaouter2003.prime_interval_nat_ladder_c01512 n (by omega) (by omega)
            · -- n <= 363937852379
              exact RamareSaouter2003.prime_interval_nat_ladder_c01511 n (by omega) (by omega)
          · -- n <= 363022981147
            exact RamareSaouter2003.prime_interval_nat_ladder_c01510 n (by omega) (by omega)
        · -- n <= 362110430863
          rcases Nat.lt_or_ge 360292269811 n with h10 | h10
          · -- n > 360292269811
            rcases Nat.lt_or_ge 361200195679 n with h12 | h12
            · -- n > 361200195679
              exact RamareSaouter2003.prime_interval_nat_ladder_c01509 n (by omega) (by omega)
            · -- n <= 361200195679
              exact RamareSaouter2003.prime_interval_nat_ladder_c01508 n (by omega) (by omega)
          · -- n <= 360292269811
            exact RamareSaouter2003.prime_interval_nat_ladder_c01507 n (by omega) (by omega)
      · -- n <= 359386647083
        rcases Nat.lt_or_ge 356683539269 n with h8 | h8
        · -- n > 356683539269
          rcases Nat.lt_or_ge 357582287681 n with h10 | h10
          · -- n > 357582287681
            rcases Nat.lt_or_ge 358483321591 n with h12 | h12
            · -- n > 358483321591
              exact RamareSaouter2003.prime_interval_nat_ladder_c01506 n (by omega) (by omega)
            · -- n <= 358483321591
              exact RamareSaouter2003.prime_interval_nat_ladder_c01505 n (by omega) (by omega)
          · -- n <= 357582287681
            exact RamareSaouter2003.prime_interval_nat_ladder_c01504 n (by omega) (by omega)
        · -- n <= 356683539269
          rcases Nat.lt_or_ge 354892875833 n with h10 | h10
          · -- n > 354892875833
            rcases Nat.lt_or_ge 355787070599 n with h12 | h12
            · -- n > 355787070599
              exact RamareSaouter2003.prime_interval_nat_ladder_c01503 n (by omega) (by omega)
            · -- n <= 355787070599
              exact RamareSaouter2003.prime_interval_nat_ladder_c01502 n (by omega) (by omega)
          · -- n <= 354892875833
            exact RamareSaouter2003.prime_interval_nat_ladder_c01501 n (by omega) (by omega)
