-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp152
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T08:04:45.80733+00:00
-- url     : https://prove2.me/submissions/2098fa80-8ebf-4a06-b694-8e8592708570

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07542
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07543
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07544
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07545
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07546
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07547
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07548
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07549
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07550
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07551
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07552
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07553
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07554
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07555
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07556
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07557
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07558
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07559
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07560
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07561
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07562
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07563
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07564
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07565
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07566
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07567
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07568
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07569
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07570
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07571
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07572
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07573
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07574
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07575
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07576
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07577
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07578
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07579
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07580
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07581
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07582
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07583
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07584
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07585
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07586
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07587
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07588
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07589
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07590

theorem solution (n : Nat)
    (hn : 4101353957833713881 < n) (hupper : n <= 4710784340673854327) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 4389310389176930827 n with h2 | h2
  · -- n > 4389310389176930827
    rcases Nat.lt_or_ge 4540783600801344271 n with h4 | h4
    · -- n > 4540783600801344271
      rcases Nat.lt_or_ge 4618469564847118361 n with h6 | h6
      · -- n > 4618469564847118361
        rcases Nat.lt_or_ge 4657809452107481893 n with h8 | h8
        · -- n > 4657809452107481893
          rcases Nat.lt_or_ge 4684221895239978631 n with h10 | h10
          · -- n > 4684221895239978631
            rcases Nat.lt_or_ge 4697484332839106363 n with h12 | h12
            · -- n > 4697484332839106363
              exact RamareSaouter2003.prime_interval_nat_ladder_c07590 n (by omega) (by omega)
            · -- n <= 4697484332839106363
              exact RamareSaouter2003.prime_interval_nat_ladder_c07589 n (by omega) (by omega)
          · -- n <= 4684221895239978631
            rcases Nat.lt_or_ge 4670997017616457271 n with h12 | h12
            · -- n > 4670997017616457271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07588 n (by omega) (by omega)
            · -- n <= 4670997017616457271
              exact RamareSaouter2003.prime_interval_nat_ladder_c07587 n (by omega) (by omega)
        · -- n <= 4657809452107481893
          rcases Nat.lt_or_ge 4631545707296787943 n with h10 | h10
          · -- n > 4631545707296787943
            rcases Nat.lt_or_ge 4644658993945219307 n with h12 | h12
            · -- n > 4644658993945219307
              exact RamareSaouter2003.prime_interval_nat_ladder_c07586 n (by omega) (by omega)
            · -- n <= 4644658993945219307
              exact RamareSaouter2003.prime_interval_nat_ladder_c07585 n (by omega) (by omega)
          · -- n <= 4631545707296787943
            exact RamareSaouter2003.prime_interval_nat_ladder_c07584 n (by omega) (by omega)
      · -- n <= 4618469564847118361
        rcases Nat.lt_or_ge 4579461822199682827 n with h8 | h8
        · -- n > 4579461822199682827
          rcases Nat.lt_or_ge 4592427676583680957 n with h10 | h10
          · -- n > 4592427676583680957
            rcases Nat.lt_or_ge 4605430225723863253 n with h12 | h12
            · -- n > 4605430225723863253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07583 n (by omega) (by omega)
            · -- n <= 4605430225723863253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07582 n (by omega) (by omega)
          · -- n <= 4592427676583680957
            exact RamareSaouter2003.prime_interval_nat_ladder_c07581 n (by omega) (by omega)
        · -- n <= 4579461822199682827
          rcases Nat.lt_or_ge 4553639947356443113 n with h10 | h10
          · -- n > 4553639947356443113
            rcases Nat.lt_or_ge 4566532700566832813 n with h12 | h12
            · -- n > 4566532700566832813
              exact RamareSaouter2003.prime_interval_nat_ladder_c07580 n (by omega) (by omega)
            · -- n <= 4566532700566832813
              exact RamareSaouter2003.prime_interval_nat_ladder_c07579 n (by omega) (by omega)
          · -- n <= 4553639947356443113
            exact RamareSaouter2003.prime_interval_nat_ladder_c07578 n (by omega) (by omega)
    · -- n <= 4540783600801344271
      rcases Nat.lt_or_ge 4464404724495535583 n with h6 | h6
      · -- n > 4464404724495535583
        rcases Nat.lt_or_ge 4502432082410252401 n with h8 | h8
        · -- n > 4502432082410252401
          rcases Nat.lt_or_ge 4515179824106243191 n with h10 | h10
          · -- n > 4515179824106243191
            rcases Nat.lt_or_ge 4527963562636296443 n with h12 | h12
            · -- n > 4527963562636296443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07577 n (by omega) (by omega)
            · -- n <= 4527963562636296443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07576 n (by omega) (by omega)
          · -- n <= 4515179824106243191
            exact RamareSaouter2003.prime_interval_nat_ladder_c07575 n (by omega) (by omega)
        · -- n <= 4502432082410252401
          rcases Nat.lt_or_ge 4477044676845044033 n with h10 | h10
          · -- n > 4477044676845044033
            rcases Nat.lt_or_ge 4489720538055618449 n with h12 | h12
            · -- n > 4489720538055618449
              exact RamareSaouter2003.prime_interval_nat_ladder_c07574 n (by omega) (by omega)
            · -- n <= 4489720538055618449
              exact RamareSaouter2003.prime_interval_nat_ladder_c07573 n (by omega) (by omega)
          · -- n <= 4477044676845044033
            exact RamareSaouter2003.prime_interval_nat_ladder_c07572 n (by omega) (by omega)
      · -- n <= 4464404724495535583
        rcases Nat.lt_or_ge 4426698386041792967 n with h8 | h8
        · -- n > 4426698386041792967
          rcases Nat.lt_or_ge 4439231637632945203 n with h10 | h10
          · -- n > 4439231637632945203
            rcases Nat.lt_or_ge 4451800439940649547 n with h12 | h12
            · -- n > 4451800439940649547
              exact RamareSaouter2003.prime_interval_nat_ladder_c07571 n (by omega) (by omega)
            · -- n <= 4451800439940649547
              exact RamareSaouter2003.prime_interval_nat_ladder_c07570 n (by omega) (by omega)
          · -- n <= 4439231637632945203
            exact RamareSaouter2003.prime_interval_nat_ladder_c07569 n (by omega) (by omega)
        · -- n <= 4426698386041792967
          rcases Nat.lt_or_ge 4401737855531127907 n with h10 | h10
          · -- n > 4401737855531127907
            rcases Nat.lt_or_ge 4414200483491061451 n with h12 | h12
            · -- n > 4414200483491061451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07568 n (by omega) (by omega)
            · -- n <= 4414200483491061451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07567 n (by omega) (by omega)
          · -- n <= 4401737855531127907
            exact RamareSaouter2003.prime_interval_nat_ladder_c07566 n (by omega) (by omega)
  · -- n <= 4389310389176930827
    rcases Nat.lt_or_ge 4242890076460945631 n with h4 | h4
    · -- n > 4242890076460945631
      rcases Nat.lt_or_ge 4315479254459039357 n with h6 | h6
      · -- n > 4315479254459039357
        rcases Nat.lt_or_ge 4352238367446553919 n with h8 | h8
        · -- n > 4352238367446553919
          rcases Nat.lt_or_ge 4364560828183790687 n with h10 | h10
          · -- n > 4364560828183790687
            rcases Nat.lt_or_ge 4376918060334370687 n with h12 | h12
            · -- n > 4376918060334370687
              exact RamareSaouter2003.prime_interval_nat_ladder_c07565 n (by omega) (by omega)
            · -- n <= 4376918060334370687
              exact RamareSaouter2003.prime_interval_nat_ladder_c07564 n (by omega) (by omega)
          · -- n <= 4364560828183790687
            exact RamareSaouter2003.prime_interval_nat_ladder_c07563 n (by omega) (by omega)
        · -- n <= 4352238367446553919
          rcases Nat.lt_or_ge 4327697695722371227 n with h10 | h10
          · -- n > 4327697695722371227
            rcases Nat.lt_or_ge 4339950708901115731 n with h12 | h12
            · -- n > 4339950708901115731
              exact RamareSaouter2003.prime_interval_nat_ladder_c07562 n (by omega) (by omega)
            · -- n <= 4339950708901115731
              exact RamareSaouter2003.prime_interval_nat_ladder_c07561 n (by omega) (by omega)
          · -- n <= 4327697695722371227
            exact RamareSaouter2003.prime_interval_nat_ladder_c07560 n (by omega) (by omega)
      · -- n <= 4315479254459039357
        rcases Nat.lt_or_ge 4279030837711759999 n with h8 | h8
        · -- n > 4279030837711759999
          rcases Nat.lt_or_ge 4291145869627278391 n with h10 | h10
          · -- n > 4291145869627278391
            rcases Nat.lt_or_ge 4303295382529273901 n with h12 | h12
            · -- n > 4303295382529273901
              exact RamareSaouter2003.prime_interval_nat_ladder_c07559 n (by omega) (by omega)
            · -- n <= 4303295382529273901
              exact RamareSaouter2003.prime_interval_nat_ladder_c07558 n (by omega) (by omega)
          · -- n <= 4291145869627278391
            exact RamareSaouter2003.prime_interval_nat_ladder_c07557 n (by omega) (by omega)
        · -- n <= 4279030837711759999
          rcases Nat.lt_or_ge 4254902916159120551 n with h10 | h10
          · -- n > 4254902916159120551
            rcases Nat.lt_or_ge 4266949833191165413 n with h12 | h12
            · -- n > 4266949833191165413
              exact RamareSaouter2003.prime_interval_nat_ladder_c07556 n (by omega) (by omega)
            · -- n <= 4266949833191165413
              exact RamareSaouter2003.prime_interval_nat_ladder_c07555 n (by omega) (by omega)
          · -- n <= 4254902916159120551
            exact RamareSaouter2003.prime_interval_nat_ladder_c07554 n (by omega) (by omega)
    · -- n <= 4242890076460945631
      rcases Nat.lt_or_ge 4171521715988451481 n with h6 | h6
      · -- n > 4171521715988451481
        rcases Nat.lt_or_ge 4207054584059092769 n with h8 | h8
        · -- n > 4207054584059092769
          rcases Nat.lt_or_ge 4218966047816865211 n with h10 | h10
          · -- n > 4218966047816865211
            rcases Nat.lt_or_ge 4230911155093670239 n with h12 | h12
            · -- n > 4230911155093670239
              exact RamareSaouter2003.prime_interval_nat_ladder_c07553 n (by omega) (by omega)
            · -- n <= 4230911155093670239
              exact RamareSaouter2003.prime_interval_nat_ladder_c07552 n (by omega) (by omega)
          · -- n <= 4218966047816865211
            exact RamareSaouter2003.prime_interval_nat_ladder_c07551 n (by omega) (by omega)
        · -- n <= 4207054584059092769
          rcases Nat.lt_or_ge 4183332532328885539 n with h10 | h10
          · -- n > 4183332532328885539
            rcases Nat.lt_or_ge 4195176791237931913 n with h12 | h12
            · -- n > 4195176791237931913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07550 n (by omega) (by omega)
            · -- n <= 4195176791237931913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07549 n (by omega) (by omega)
          · -- n <= 4183332532328885539
            exact RamareSaouter2003.prime_interval_nat_ladder_c07548 n (by omega) (by omega)
      · -- n <= 4171521715988451481
        rcases Nat.lt_or_ge 4136289018368522989 n with h8 | h8
        · -- n > 4136289018368522989
          rcases Nat.lt_or_ge 4148000045733545179 n with h10 | h10
          · -- n > 4148000045733545179
            rcases Nat.lt_or_ge 4159744209706156913 n with h12 | h12
            · -- n > 4159744209706156913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07547 n (by omega) (by omega)
            · -- n <= 4159744209706156913
              exact RamareSaouter2003.prime_interval_nat_ladder_c07546 n (by omega) (by omega)
          · -- n <= 4148000045733545179
            exact RamareSaouter2003.prime_interval_nat_ladder_c07545 n (by omega) (by omega)
        · -- n <= 4136289018368522989
          rcases Nat.lt_or_ge 4112966068480500767 n with h10 | h10
          · -- n > 4112966068480500767
            rcases Nat.lt_or_ge 4124611004666130701 n with h12 | h12
            · -- n > 4124611004666130701
              exact RamareSaouter2003.prime_interval_nat_ladder_c07544 n (by omega) (by omega)
            · -- n <= 4124611004666130701
              exact RamareSaouter2003.prime_interval_nat_ladder_c07543 n (by omega) (by omega)
          · -- n <= 4112966068480500767
            exact RamareSaouter2003.prime_interval_nat_ladder_c07542 n (by omega) (by omega)
