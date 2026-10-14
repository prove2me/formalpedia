-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp172
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T15:42:10.856024+00:00
-- url     : https://prove2.me/submissions/008b0a4d-74f0-4baa-a058-dea9edee3b6d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08541
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08550
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08570

theorem solution (n : Nat)
    (hn : 55110872013924363761 < n) (hupper : n <= 62115373307991419869) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 58437008053202423153 n with h2 | h2
  · -- n > 58437008053202423153
    rcases Nat.lt_or_ge 60174613313063934577 n with h4 | h4
    · -- n > 60174613313063934577
      rcases Nat.lt_or_ge 61062695850637498363 n with h6 | h6
      · -- n > 61062695850637498363
        rcases Nat.lt_or_ge 61511641038264038591 n with h8 | h8
        · -- n > 61511641038264038591
          rcases Nat.lt_or_ge 61812770078083805161 n with h10 | h10
          · -- n > 61812770078083805161
            rcases Nat.lt_or_ge 61963887004652987401 n with h12 | h12
            · -- n > 61963887004652987401
              exact RamareSaouter2003.prime_interval_nat_ladder_c08570 n (by omega) (by omega)
            · -- n <= 61963887004652987401
              exact RamareSaouter2003.prime_interval_nat_ladder_c08569 n (by omega) (by omega)
          · -- n <= 61812770078083805161
            rcases Nat.lt_or_ge 61662021788340306803 n with h12 | h12
            · -- n > 61662021788340306803
              exact RamareSaouter2003.prime_interval_nat_ladder_c08568 n (by omega) (by omega)
            · -- n <= 61662021788340306803
              exact RamareSaouter2003.prime_interval_nat_ladder_c08567 n (by omega) (by omega)
        · -- n <= 61511641038264038591
          rcases Nat.lt_or_ge 61211979092422996921 n with h10 | h10
          · -- n > 61211979092422996921
            rcases Nat.lt_or_ge 61361627124256483523 n with h12 | h12
            · -- n > 61361627124256483523
              exact RamareSaouter2003.prime_interval_nat_ladder_c08566 n (by omega) (by omega)
            · -- n <= 61361627124256483523
              exact RamareSaouter2003.prime_interval_nat_ladder_c08565 n (by omega) (by omega)
          · -- n <= 61211979092422996921
            exact RamareSaouter2003.prime_interval_nat_ladder_c08564 n (by omega) (by omega)
      · -- n <= 61062695850637498363
        rcases Nat.lt_or_ge 60617027732976324601 n with h8 | h8
        · -- n > 60617027732976324601
          rcases Nat.lt_or_ge 60765221397901290979 n with h10 | h10
          · -- n > 60765221397901290979
            rcases Nat.lt_or_ge 60913777185172041913 n with h12 | h12
            · -- n > 60913777185172041913
              exact RamareSaouter2003.prime_interval_nat_ladder_c08563 n (by omega) (by omega)
            · -- n <= 60913777185172041913
              exact RamareSaouter2003.prime_interval_nat_ladder_c08562 n (by omega) (by omega)
          · -- n <= 60765221397901290979
            exact RamareSaouter2003.prime_interval_nat_ladder_c08561 n (by omega) (by omega)
        · -- n <= 60617027732976324601
          rcases Nat.lt_or_ge 60321723900589244773 n with h10 | h10
          · -- n > 60321723900589244773
            rcases Nat.lt_or_ge 60469195636317813977 n with h12 | h12
            · -- n > 60469195636317813977
              exact RamareSaouter2003.prime_interval_nat_ladder_c08560 n (by omega) (by omega)
            · -- n <= 60469195636317813977
              exact RamareSaouter2003.prime_interval_nat_ladder_c08559 n (by omega) (by omega)
          · -- n <= 60321723900589244773
            exact RamareSaouter2003.prime_interval_nat_ladder_c08558 n (by omega) (by omega)
    · -- n <= 60174613313063934577
      rcases Nat.lt_or_ge 59299446657039627053 n with h6 | h6
      · -- n > 59299446657039627053
        rcases Nat.lt_or_ge 59735427230725522519 n with h8 | h8
        · -- n > 59735427230725522519
          rcases Nat.lt_or_ge 59881465616162439629 n with h10 | h10
          · -- n > 59881465616162439629
            rcases Nat.lt_or_ge 60027860076957017243 n with h12 | h12
            · -- n > 60027860076957017243
              exact RamareSaouter2003.prime_interval_nat_ladder_c08557 n (by omega) (by omega)
            · -- n <= 60027860076957017243
              exact RamareSaouter2003.prime_interval_nat_ladder_c08556 n (by omega) (by omega)
          · -- n <= 59881465616162439629
            exact RamareSaouter2003.prime_interval_nat_ladder_c08555 n (by omega) (by omega)
        · -- n <= 59735427230725522519
          rcases Nat.lt_or_ge 59444418402743146777 n with h10 | h10
          · -- n > 59444418402743146777
            rcases Nat.lt_or_ge 59589745259892280157 n with h12 | h12
            · -- n > 59589745259892280157
              exact RamareSaouter2003.prime_interval_nat_ladder_c08554 n (by omega) (by omega)
            · -- n <= 59589745259892280157
              exact RamareSaouter2003.prime_interval_nat_ladder_c08553 n (by omega) (by omega)
          · -- n <= 59444418402743146777
            exact RamareSaouter2003.prime_interval_nat_ladder_c08552 n (by omega) (by omega)
      · -- n <= 59299446657039627053
        rcases Nat.lt_or_ge 58866647413757834653 n with h8 | h8
        · -- n > 58866647413757834653
          rcases Nat.lt_or_ge 59010561653468942287 n with h10 | h10
          · -- n > 59010561653468942287
            rcases Nat.lt_or_ge 59154827848230417829 n with h12 | h12
            · -- n > 59154827848230417829
              exact RamareSaouter2003.prime_interval_nat_ladder_c08551 n (by omega) (by omega)
            · -- n <= 59154827848230417829
              exact RamareSaouter2003.prime_interval_nat_ladder_c08550 n (by omega) (by omega)
          · -- n <= 59010561653468942287
            exact RamareSaouter2003.prime_interval_nat_ladder_c08549 n (by omega) (by omega)
        · -- n <= 58866647413757834653
          rcases Nat.lt_or_ge 58579872036438698893 n with h10 | h10
          · -- n > 58579872036438698893
            rcases Nat.lt_or_ge 58723084283731609253 n with h12 | h12
            · -- n > 58723084283731609253
              exact RamareSaouter2003.prime_interval_nat_ladder_c08548 n (by omega) (by omega)
            · -- n <= 58723084283731609253
              exact RamareSaouter2003.prime_interval_nat_ladder_c08547 n (by omega) (by omega)
          · -- n <= 58579872036438698893
            exact RamareSaouter2003.prime_interval_nat_ladder_c08546 n (by omega) (by omega)
  · -- n <= 58437008053202423153
    rcases Nat.lt_or_ge 56749576813895141851 n with h4 | h4
    · -- n > 56749576813895141851
      rcases Nat.lt_or_ge 57587111156558068187 n with h6 | h6
      · -- n > 57587111156558068187
        rcases Nat.lt_or_ge 58010503152120180853 n with h8 | h8
        · -- n > 58010503152120180853
          rcases Nat.lt_or_ge 58152324399777786667 n with h10 | h10
          · -- n > 58152324399777786667
            rcases Nat.lt_or_ge 58294492386829128797 n with h12 | h12
            · -- n > 58294492386829128797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08545 n (by omega) (by omega)
            · -- n <= 58294492386829128797
              exact RamareSaouter2003.prime_interval_nat_ladder_c08544 n (by omega) (by omega)
          · -- n <= 58152324399777786667
            exact RamareSaouter2003.prime_interval_nat_ladder_c08543 n (by omega) (by omega)
        · -- n <= 58010503152120180853
          rcases Nat.lt_or_ge 57727897390973868983 n with h10 | h10
          · -- n > 57727897390973868983
            rcases Nat.lt_or_ge 57869027749221938033 n with h12 | h12
            · -- n > 57869027749221938033
              exact RamareSaouter2003.prime_interval_nat_ladder_c08542 n (by omega) (by omega)
            · -- n <= 57869027749221938033
              exact RamareSaouter2003.prime_interval_nat_ladder_c08541 n (by omega) (by omega)
          · -- n <= 57727897390973868983
            exact RamareSaouter2003.prime_interval_nat_ladder_c08540 n (by omega) (by omega)
      · -- n <= 57587111156558068187
        rcases Nat.lt_or_ge 57166810643405736563 n with h8 | h8
        · -- n > 57166810643405736563
          rcases Nat.lt_or_ge 57306569275480855621 n with h10 | h10
          · -- n > 57306569275480855621
            rcases Nat.lt_or_ge 57446669010969976363 n with h12 | h12
            · -- n > 57446669010969976363
              exact RamareSaouter2003.prime_interval_nat_ladder_c08539 n (by omega) (by omega)
            · -- n <= 57446669010969976363
              exact RamareSaouter2003.prime_interval_nat_ladder_c08538 n (by omega) (by omega)
          · -- n <= 57306569275480855621
            exact RamareSaouter2003.prime_interval_nat_ladder_c08537 n (by omega) (by omega)
        · -- n <= 57166810643405736563
          rcases Nat.lt_or_ge 56888315419846578601 n with h10 | h10
          · -- n > 56888315419846578601
            rcases Nat.lt_or_ge 57027393156345335161 n with h12 | h12
            · -- n > 57027393156345335161
              exact RamareSaouter2003.prime_interval_nat_ladder_c08536 n (by omega) (by omega)
            · -- n <= 57027393156345335161
              exact RamareSaouter2003.prime_interval_nat_ladder_c08535 n (by omega) (by omega)
          · -- n <= 56888315419846578601
            exact RamareSaouter2003.prime_interval_nat_ladder_c08534 n (by omega) (by omega)
    · -- n <= 56749576813895141851
      rcases Nat.lt_or_ge 55924222458725995643 n with h6 | h6
      · -- n > 55924222458725995643
        rcases Nat.lt_or_ge 56335388127513964669 n with h8 | h8
        · -- n > 56335388127513964669
          rcases Nat.lt_or_ge 56473114132194391913 n with h10 | h10
          · -- n > 56473114132194391913
            rcases Nat.lt_or_ge 56611176550157079013 n with h12 | h12
            · -- n > 56611176550157079013
              exact RamareSaouter2003.prime_interval_nat_ladder_c08533 n (by omega) (by omega)
            · -- n <= 56611176550157079013
              exact RamareSaouter2003.prime_interval_nat_ladder_c08532 n (by omega) (by omega)
          · -- n <= 56473114132194391913
            exact RamareSaouter2003.prime_interval_nat_ladder_c08531 n (by omega) (by omega)
        · -- n <= 56335388127513964669
          rcases Nat.lt_or_ge 56060943130519077299 n with h10 | h10
          · -- n > 56060943130519077299
            rcases Nat.lt_or_ge 56197998314599890179 n with h12 | h12
            · -- n > 56197998314599890179
              exact RamareSaouter2003.prime_interval_nat_ladder_c08530 n (by omega) (by omega)
            · -- n <= 56197998314599890179
              exact RamareSaouter2003.prime_interval_nat_ladder_c08529 n (by omega) (by omega)
          · -- n <= 56060943130519077299
            exact RamareSaouter2003.prime_interval_nat_ladder_c08528 n (by omega) (by omega)
      · -- n <= 55924222458725995643
        rcases Nat.lt_or_ge 55516057608694598737 n with h8 | h8
        · -- n > 55516057608694598737
          rcases Nat.lt_or_ge 55651780515691174459 n with h10 | h10
          · -- n > 55651780515691174459
            rcases Nat.lt_or_ge 55787835238363658741 n with h12 | h12
            · -- n > 55787835238363658741
              exact RamareSaouter2003.prime_interval_nat_ladder_c08527 n (by omega) (by omega)
            · -- n <= 55787835238363658741
              exact RamareSaouter2003.prime_interval_nat_ladder_c08526 n (by omega) (by omega)
          · -- n <= 55651780515691174459
            exact RamareSaouter2003.prime_interval_nat_ladder_c08525 n (by omega) (by omega)
        · -- n <= 55516057608694598737
          rcases Nat.lt_or_ge 55245603769223516503 n with h10 | h10
          · -- n > 55245603769223516503
            rcases Nat.lt_or_ge 55380665566384808261 n with h12 | h12
            · -- n > 55380665566384808261
              exact RamareSaouter2003.prime_interval_nat_ladder_c08524 n (by omega) (by omega)
            · -- n <= 55380665566384808261
              exact RamareSaouter2003.prime_interval_nat_ladder_c08523 n (by omega) (by omega)
          · -- n <= 55245603769223516503
            exact RamareSaouter2003.prime_interval_nat_ladder_c08522 n (by omega) (by omega)
