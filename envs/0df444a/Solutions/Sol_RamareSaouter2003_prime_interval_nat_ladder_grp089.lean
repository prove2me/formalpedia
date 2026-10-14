-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp089
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T10:46:25.070695+00:00
-- url     : https://prove2.me/submissions/ef969f5e-b799-4c29-aca5-2bb78b203741

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04401
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04402
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04403
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04404
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04405
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04406
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04407
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04408
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04409
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04410
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04411
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04412
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04413
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04414
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04415
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04416
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04417
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04418
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04419
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04420
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04421
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04422
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04423
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04424
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04425
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04426
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04427
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04428
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04429
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04430
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04431
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04432
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04433
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04434
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04435
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04436
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04437
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04438
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04439
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04440
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04441
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04442
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04443
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04444
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04445
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04446
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04447
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04448
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04449
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04450

theorem solution (n : Nat)
    (hn : 570899461905341 < n) (hupper : n <= 657550128634237) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 612701177486971 n with h2 | h2
  · -- n > 612701177486971
    rcases Nat.lt_or_ge 633832353266599 n with h4 | h4
    · -- n > 633832353266599
      rcases Nat.lt_or_ge 644670802715053 n with h6 | h6
      · -- n > 644670802715053
        rcases Nat.lt_or_ge 650158166365787 n with h8 | h8
        · -- n > 650158166365787
          rcases Nat.lt_or_ge 653843735076703 n with h10 | h10
          · -- n > 653843735076703
            rcases Nat.lt_or_ge 655694034722147 n with h12 | h12
            · -- n > 655694034722147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04450 n (by omega) (by omega)
            · -- n <= 655694034722147
              exact RamareSaouter2003.prime_interval_nat_ladder_c04449 n (by omega) (by omega)
          · -- n <= 653843735076703
            rcases Nat.lt_or_ge 651997938026257 n with h12 | h12
            · -- n > 651997938026257
              exact RamareSaouter2003.prime_interval_nat_ladder_c04448 n (by omega) (by omega)
            · -- n <= 651997938026257
              exact RamareSaouter2003.prime_interval_nat_ladder_c04447 n (by omega) (by omega)
        · -- n <= 650158166365787
          rcases Nat.lt_or_ge 646492830892547 n with h10 | h10
          · -- n > 646492830892547
            rcases Nat.lt_or_ge 648322829735407 n with h12 | h12
            · -- n > 648322829735407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04446 n (by omega) (by omega)
            · -- n <= 648322829735407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04445 n (by omega) (by omega)
          · -- n <= 646492830892547
            exact RamareSaouter2003.prime_interval_nat_ladder_c04444 n (by omega) (by omega)
      · -- n <= 644670802715053
        rcases Nat.lt_or_ge 639229701594929 n with h8 | h8
        · -- n > 639229701594929
          rcases Nat.lt_or_ge 641038763789693 n with h10 | h10
          · -- n > 641038763789693
            rcases Nat.lt_or_ge 642852055115189 n with h12 | h12
            · -- n > 642852055115189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04443 n (by omega) (by omega)
            · -- n <= 642852055115189
              exact RamareSaouter2003.prime_interval_nat_ladder_c04442 n (by omega) (by omega)
          · -- n <= 641038763789693
            exact RamareSaouter2003.prime_interval_nat_ladder_c04441 n (by omega) (by omega)
        · -- n <= 639229701594929
          rcases Nat.lt_or_ge 635625698952857 n with h10 | h10
          · -- n > 635625698952857
            rcases Nat.lt_or_ge 637425315172861 n with h12 | h12
            · -- n > 637425315172861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04440 n (by omega) (by omega)
            · -- n <= 637425315172861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04439 n (by omega) (by omega)
          · -- n <= 635625698952857
            exact RamareSaouter2003.prime_interval_nat_ladder_c04438 n (by omega) (by omega)
    · -- n <= 633832353266599
      rcases Nat.lt_or_ge 623178596948933 n with h6 | h6
      · -- n > 623178596948933
        rcases Nat.lt_or_ge 628483307968277 n with h8 | h8
        · -- n > 628483307968277
          rcases Nat.lt_or_ge 630261142357229 n with h10 | h10
          · -- n > 630261142357229
            rcases Nat.lt_or_ge 632042996768903 n with h12 | h12
            · -- n > 632042996768903
              exact RamareSaouter2003.prime_interval_nat_ladder_c04437 n (by omega) (by omega)
            · -- n <= 632042996768903
              exact RamareSaouter2003.prime_interval_nat_ladder_c04436 n (by omega) (by omega)
          · -- n <= 630261142357229
            exact RamareSaouter2003.prime_interval_nat_ladder_c04435 n (by omega) (by omega)
        · -- n <= 628483307968277
          rcases Nat.lt_or_ge 624942218587217 n with h10 | h10
          · -- n > 624942218587217
            rcases Nat.lt_or_ge 626709333929741 n with h12 | h12
            · -- n > 626709333929741
              exact RamareSaouter2003.prime_interval_nat_ladder_c04434 n (by omega) (by omega)
            · -- n <= 626709333929741
              exact RamareSaouter2003.prime_interval_nat_ladder_c04433 n (by omega) (by omega)
          · -- n <= 624942218587217
            exact RamareSaouter2003.prime_interval_nat_ladder_c04432 n (by omega) (by omega)
      · -- n <= 623178596948933
        rcases Nat.lt_or_ge 617917945673153 n with h8 | h8
        · -- n > 617917945673153
          rcases Nat.lt_or_ge 619665947812237 n with h10 | h10
          · -- n > 619665947812237
            rcases Nat.lt_or_ge 621419810529173 n with h12 | h12
            · -- n > 621419810529173
              exact RamareSaouter2003.prime_interval_nat_ladder_c04431 n (by omega) (by omega)
            · -- n <= 621419810529173
              exact RamareSaouter2003.prime_interval_nat_ladder_c04430 n (by omega) (by omega)
          · -- n <= 619665947812237
            exact RamareSaouter2003.prime_interval_nat_ladder_c04429 n (by omega) (by omega)
        · -- n <= 617917945673153
          rcases Nat.lt_or_ge 614434750756367 n with h10 | h10
          · -- n > 614434750756367
            rcases Nat.lt_or_ge 616174397349583 n with h12 | h12
            · -- n > 616174397349583
              exact RamareSaouter2003.prime_interval_nat_ladder_c04428 n (by omega) (by omega)
            · -- n <= 616174397349583
              exact RamareSaouter2003.prime_interval_nat_ladder_c04427 n (by omega) (by omega)
          · -- n <= 614434750756367
            exact RamareSaouter2003.prime_interval_nat_ladder_c04426 n (by omega) (by omega)
  · -- n <= 612701177486971
    rcases Nat.lt_or_ge 590592912236989 n with h4 | h4
    · -- n > 590592912236989
      rcases Nat.lt_or_ge 600695513896403 n with h6 | h6
      · -- n > 600695513896403
        rcases Nat.lt_or_ge 605811702371731 n with h8 | h8
        · -- n > 605811702371731
          rcases Nat.lt_or_ge 609246557566597 n with h10 | h10
          · -- n > 609246557566597
            rcases Nat.lt_or_ge 610971486053119 n with h12 | h12
            · -- n > 610971486053119
              exact RamareSaouter2003.prime_interval_nat_ladder_c04425 n (by omega) (by omega)
            · -- n <= 610971486053119
              exact RamareSaouter2003.prime_interval_nat_ladder_c04424 n (by omega) (by omega)
          · -- n <= 609246557566597
            rcases Nat.lt_or_ge 607526832469057 n with h12 | h12
            · -- n > 607526832469057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04423 n (by omega) (by omega)
            · -- n <= 607526832469057
              exact RamareSaouter2003.prime_interval_nat_ladder_c04422 n (by omega) (by omega)
        · -- n <= 605811702371731
          rcases Nat.lt_or_ge 602396125516517 n with h10 | h10
          · -- n > 602396125516517
            rcases Nat.lt_or_ge 604101454121861 n with h12 | h12
            · -- n > 604101454121861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04421 n (by omega) (by omega)
            · -- n <= 604101454121861
              exact RamareSaouter2003.prime_interval_nat_ladder_c04420 n (by omega) (by omega)
          · -- n <= 602396125516517
            exact RamareSaouter2003.prime_interval_nat_ladder_c04419 n (by omega) (by omega)
      · -- n <= 600695513896403
        rcases Nat.lt_or_ge 595622496697693 n with h8 | h8
        · -- n > 595622496697693
          rcases Nat.lt_or_ge 597308830651651 n with h10 | h10
          · -- n > 597308830651651
            rcases Nat.lt_or_ge 598999703296843 n with h12 | h12
            · -- n > 598999703296843
              exact RamareSaouter2003.prime_interval_nat_ladder_c04418 n (by omega) (by omega)
            · -- n <= 598999703296843
              exact RamareSaouter2003.prime_interval_nat_ladder_c04417 n (by omega) (by omega)
          · -- n <= 597308830651651
            exact RamareSaouter2003.prime_interval_nat_ladder_c04416 n (by omega) (by omega)
        · -- n <= 595622496697693
          rcases Nat.lt_or_ge 592264960125017 n with h10 | h10
          · -- n > 592264960125017
            rcases Nat.lt_or_ge 593941763219797 n with h12 | h12
            · -- n > 593941763219797
              exact RamareSaouter2003.prime_interval_nat_ladder_c04415 n (by omega) (by omega)
            · -- n <= 593941763219797
              exact RamareSaouter2003.prime_interval_nat_ladder_c04414 n (by omega) (by omega)
          · -- n <= 592264960125017
            exact RamareSaouter2003.prime_interval_nat_ladder_c04413 n (by omega) (by omega)
    · -- n <= 590592912236989
      rcases Nat.lt_or_ge 580663793845279 n with h6 | h6
      · -- n > 580663793845279
        rcases Nat.lt_or_ge 585607836251531 n with h8 | h8
        · -- n > 585607836251531
          rcases Nat.lt_or_ge 587263028068273 n with h10 | h10
          · -- n > 587263028068273
            rcases Nat.lt_or_ge 588925605188407 n with h12 | h12
            · -- n > 588925605188407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04412 n (by omega) (by omega)
            · -- n <= 588925605188407
              exact RamareSaouter2003.prime_interval_nat_ladder_c04411 n (by omega) (by omega)
          · -- n <= 587263028068273
            exact RamareSaouter2003.prime_interval_nat_ladder_c04410 n (by omega) (by omega)
        · -- n <= 585607836251531
          rcases Nat.lt_or_ge 582307548335657 n with h10 | h10
          · -- n > 582307548335657
            rcases Nat.lt_or_ge 583955318726729 n with h12 | h12
            · -- n > 583955318726729
              exact RamareSaouter2003.prime_interval_nat_ladder_c04409 n (by omega) (by omega)
            · -- n <= 583955318726729
              exact RamareSaouter2003.prime_interval_nat_ladder_c04408 n (by omega) (by omega)
          · -- n <= 582307548335657
            exact RamareSaouter2003.prime_interval_nat_ladder_c04407 n (by omega) (by omega)
      · -- n <= 580663793845279
        rcases Nat.lt_or_ge 575760144620849 n with h8 | h8
        · -- n > 575760144620849
          rcases Nat.lt_or_ge 577390125407443 n with h10 | h10
          · -- n > 577390125407443
            rcases Nat.lt_or_ge 579024671584939 n with h12 | h12
            · -- n > 579024671584939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04406 n (by omega) (by omega)
            · -- n <= 579024671584939
              exact RamareSaouter2003.prime_interval_nat_ladder_c04405 n (by omega) (by omega)
          · -- n <= 577390125407443
            exact RamareSaouter2003.prime_interval_nat_ladder_c04404 n (by omega) (by omega)
        · -- n <= 575760144620849
          rcases Nat.lt_or_ge 572514751605361 n with h10 | h10
          · -- n > 572514751605361
            rcases Nat.lt_or_ge 574134960010561 n with h12 | h12
            · -- n > 574134960010561
              exact RamareSaouter2003.prime_interval_nat_ladder_c04403 n (by omega) (by omega)
            · -- n <= 574134960010561
              exact RamareSaouter2003.prime_interval_nat_ladder_c04402 n (by omega) (by omega)
          · -- n <= 572514751605361
            exact RamareSaouter2003.prime_interval_nat_ladder_c04401 n (by omega) (by omega)
