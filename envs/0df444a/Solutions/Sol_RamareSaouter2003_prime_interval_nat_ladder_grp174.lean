-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp174
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T16:33:36.539745+00:00
-- url     : https://prove2.me/submissions/39e1b41e-2aab-42ce-8e8f-c9a2d754c769

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08620
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08621
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08622
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08623
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08624
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08625
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08626
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08627
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08628
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08629
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08630
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08631
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08632
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08633
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08634
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08635
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08636
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08637
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08638
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08639
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08640
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08641
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08642
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08643
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08644
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08645
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08646
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08647
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08648
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08649
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08650
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08651
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08652
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08653
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08654
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08655
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08656
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08657
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08658
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08659
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08660
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08661
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08662
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08663
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08664
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08665
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08666
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08667
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c08668

theorem solution (n : Nat)
    (hn : 70010134047899070677 < n) (hupper : n <= 78908309765868443269) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 74235492713880295387 n with h2 | h2
  · -- n > 74235492713880295387
    rcases Nat.lt_or_ge 76442862500235983189 n with h4 | h4
    · -- n > 76442862500235983189
      rcases Nat.lt_or_ge 77571040617569642317 n with h6 | h6
      · -- n > 77571040617569642317
        rcases Nat.lt_or_ge 78141358459551321589 n with h8 | h8
        · -- n > 78141358459551321589
          rcases Nat.lt_or_ge 78523897416094540271 n with h10 | h10
          · -- n > 78523897416094540271
            rcases Nat.lt_or_ge 78715868879465317343 n with h12 | h12
            · -- n > 78715868879465317343
              exact RamareSaouter2003.prime_interval_nat_ladder_c08668 n (by omega) (by omega)
            · -- n <= 78715868879465317343
              exact RamareSaouter2003.prime_interval_nat_ladder_c08667 n (by omega) (by omega)
          · -- n <= 78523897416094540271
            rcases Nat.lt_or_ge 78332394156322157101 n with h12 | h12
            · -- n > 78332394156322157101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08666 n (by omega) (by omega)
            · -- n <= 78332394156322157101
              exact RamareSaouter2003.prime_interval_nat_ladder_c08665 n (by omega) (by omega)
        · -- n <= 78141358459551321589
          rcases Nat.lt_or_ge 77760682514468702759 n with h10 | h10
          · -- n > 77760682514468702759
            rcases Nat.lt_or_ge 77950788160573964227 n with h12 | h12
            · -- n > 77950788160573964227
              exact RamareSaouter2003.prime_interval_nat_ladder_c08664 n (by omega) (by omega)
            · -- n <= 77950788160573964227
              exact RamareSaouter2003.prime_interval_nat_ladder_c08663 n (by omega) (by omega)
          · -- n <= 77760682514468702759
            exact RamareSaouter2003.prime_interval_nat_ladder_c08662 n (by omega) (by omega)
      · -- n <= 77571040617569642317
        rcases Nat.lt_or_ge 77004885368022455453 n with h8 | h8
        · -- n > 77004885368022455453
          rcases Nat.lt_or_ge 77193143083969849289 n with h10 | h10
          · -- n > 77193143083969849289
            rcases Nat.lt_or_ge 77381861286683776597 n with h12 | h12
            · -- n > 77381861286683776597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08661 n (by omega) (by omega)
            · -- n <= 77381861286683776597
              exact RamareSaouter2003.prime_interval_nat_ladder_c08660 n (by omega) (by omega)
          · -- n <= 77193143083969849289
            exact RamareSaouter2003.prime_interval_nat_ladder_c08659 n (by omega) (by omega)
        · -- n <= 77004885368022455453
          rcases Nat.lt_or_ge 76629746193341584121 n with h10 | h10
          · -- n > 76629746193341584121
            rcases Nat.lt_or_ge 76817087035679493593 n with h12 | h12
            · -- n > 76817087035679493593
              exact RamareSaouter2003.prime_interval_nat_ladder_c08658 n (by omega) (by omega)
            · -- n <= 76817087035679493593
              exact RamareSaouter2003.prime_interval_nat_ladder_c08657 n (by omega) (by omega)
          · -- n <= 76629746193341584121
            exact RamareSaouter2003.prime_interval_nat_ladder_c08656 n (by omega) (by omega)
    · -- n <= 76442862500235983189
      rcases Nat.lt_or_ge 75331092356897422687 n with h6 | h6
      · -- n > 75331092356897422687
        rcases Nat.lt_or_ge 75884941529120220059 n with h8 | h8
        · -- n > 75884941529120220059
          rcases Nat.lt_or_ge 76070460964237296523 n with h10 | h10
          · -- n > 76070460964237296523
            rcases Nat.lt_or_ge 76256434343514070469 n with h12 | h12
            · -- n > 76256434343514070469
              exact RamareSaouter2003.prime_interval_nat_ladder_c08655 n (by omega) (by omega)
            · -- n <= 76256434343514070469
              exact RamareSaouter2003.prime_interval_nat_ladder_c08654 n (by omega) (by omega)
          · -- n <= 76070460964237296523
            exact RamareSaouter2003.prime_interval_nat_ladder_c08653 n (by omega) (by omega)
        · -- n <= 75884941529120220059
          rcases Nat.lt_or_ge 75515257824928278673 n with h10 | h10
          · -- n > 75515257824928278673
            rcases Nat.lt_or_ge 75699874002880800919 n with h12 | h12
            · -- n > 75699874002880800919
              exact RamareSaouter2003.prime_interval_nat_ladder_c08652 n (by omega) (by omega)
            · -- n <= 75699874002880800919
              exact RamareSaouter2003.prime_interval_nat_ladder_c08651 n (by omega) (by omega)
          · -- n <= 75515257824928278673
            exact RamareSaouter2003.prime_interval_nat_ladder_c08650 n (by omega) (by omega)
      · -- n <= 75331092356897422687
        rcases Nat.lt_or_ge 74781286413386973533 n with h8 | h8
        · -- n > 74781286413386973533
          rcases Nat.lt_or_ge 74964107133800206499 n with h10 | h10
          · -- n > 74964107133800206499
            rcases Nat.lt_or_ge 75147375682062579503 n with h12 | h12
            · -- n > 75147375682062579503
              exact RamareSaouter2003.prime_interval_nat_ladder_c08649 n (by omega) (by omega)
            · -- n <= 75147375682062579503
              exact RamareSaouter2003.prime_interval_nat_ladder_c08648 n (by omega) (by omega)
          · -- n <= 74964107133800206499
            exact RamareSaouter2003.prime_interval_nat_ladder_c08647 n (by omega) (by omega)
        · -- n <= 74781286413386973533
          rcases Nat.lt_or_ge 74416979731173230947 n with h10 | h10
          · -- n > 74416979731173230947
            rcases Nat.lt_or_ge 74598910831805113531 n with h12 | h12
            · -- n > 74598910831805113531
              exact RamareSaouter2003.prime_interval_nat_ladder_c08646 n (by omega) (by omega)
            · -- n <= 74598910831805113531
              exact RamareSaouter2003.prime_interval_nat_ladder_c08645 n (by omega) (by omega)
          · -- n <= 74416979731173230947
            exact RamareSaouter2003.prime_interval_nat_ladder_c08644 n (by omega) (by omega)
  · -- n <= 74235492713880295387
    rcases Nat.lt_or_ge 72091863123674038439 n with h4 | h4
    · -- n > 72091863123674038439
      rcases Nat.lt_or_ge 73155826638956814617 n with h6 | h6
      · -- n > 73155826638956814617
        rcases Nat.lt_or_ge 73693682305503416201 n with h8 | h8
        · -- n > 73693682305503416201
          rcases Nat.lt_or_ge 73873845143000886281 n with h10 | h10
          · -- n > 73873845143000886281
            rcases Nat.lt_or_ge 74054448189619472291 n with h12 | h12
            · -- n > 74054448189619472291
              exact RamareSaouter2003.prime_interval_nat_ladder_c08643 n (by omega) (by omega)
            · -- n <= 74054448189619472291
              exact RamareSaouter2003.prime_interval_nat_ladder_c08642 n (by omega) (by omega)
          · -- n <= 73873845143000886281
            exact RamareSaouter2003.prime_interval_nat_ladder_c08641 n (by omega) (by omega)
        · -- n <= 73693682305503416201
          rcases Nat.lt_or_ge 73334674267449939713 n with h10 | h10
          · -- n > 73334674267449939713
            rcases Nat.lt_or_ge 73513958901567165173 n with h12 | h12
            · -- n > 73513958901567165173
              exact RamareSaouter2003.prime_interval_nat_ladder_c08640 n (by omega) (by omega)
            · -- n <= 73513958901567165173
              exact RamareSaouter2003.prime_interval_nat_ladder_c08639 n (by omega) (by omega)
          · -- n <= 73334674267449939713
            exact RamareSaouter2003.prime_interval_nat_ladder_c08638 n (by omega) (by omega)
      · -- n <= 73155826638956814617
        rcases Nat.lt_or_ge 72621896680638319099 n with h8 | h8
        · -- n > 72621896680638319099
          rcases Nat.lt_or_ge 72799439257839520073 n with h10 | h10
          · -- n > 72799439257839520073
            rcases Nat.lt_or_ge 72977414876513492731 n with h12 | h12
            · -- n > 72977414876513492731
              exact RamareSaouter2003.prime_interval_nat_ladder_c08637 n (by omega) (by omega)
            · -- n <= 72977414876513492731
              exact RamareSaouter2003.prime_interval_nat_ladder_c08636 n (by omega) (by omega)
          · -- n <= 72799439257839520073
            exact RamareSaouter2003.prime_interval_nat_ladder_c08635 n (by omega) (by omega)
        · -- n <= 72621896680638319099
          rcases Nat.lt_or_ge 72268109685880208119 n with h10 | h10
          · -- n > 72268109685880208119
            rcases Nat.lt_or_ge 72444787121420868331 n with h12 | h12
            · -- n > 72444787121420868331
              exact RamareSaouter2003.prime_interval_nat_ladder_c08634 n (by omega) (by omega)
            · -- n <= 72444787121420868331
              exact RamareSaouter2003.prime_interval_nat_ladder_c08633 n (by omega) (by omega)
          · -- n <= 72268109685880208119
            exact RamareSaouter2003.prime_interval_nat_ladder_c08632 n (by omega) (by omega)
    · -- n <= 72091863123674038439
      rcases Nat.lt_or_ge 71043373567402497409 n with h6 | h6
      · -- n > 71043373567402497409
        rcases Nat.lt_or_ge 71565698291304771523 n with h8 | h8
        · -- n > 71565698291304771523
          rcases Nat.lt_or_ge 71740658463523052249 n with h10 | h10
          · -- n > 71740658463523052249
            rcases Nat.lt_or_ge 71916046424829404071 n with h12 | h12
            · -- n > 71916046424829404071
              exact RamareSaouter2003.prime_interval_nat_ladder_c08631 n (by omega) (by omega)
            · -- n <= 71916046424829404071
              exact RamareSaouter2003.prime_interval_nat_ladder_c08630 n (by omega) (by omega)
          · -- n <= 71740658463523052249
            exact RamareSaouter2003.prime_interval_nat_ladder_c08629 n (by omega) (by omega)
        · -- n <= 71565698291304771523
          rcases Nat.lt_or_ge 71217056833043159431 n with h10 | h10
          · -- n > 71217056833043159431
            rcases Nat.lt_or_ge 71391164882503040027 n with h12 | h12
            · -- n > 71391164882503040027
              exact RamareSaouter2003.prime_interval_nat_ladder_c08628 n (by omega) (by omega)
            · -- n <= 71391164882503040027
              exact RamareSaouter2003.prime_interval_nat_ladder_c08627 n (by omega) (by omega)
          · -- n <= 71217056833043159431
            exact RamareSaouter2003.prime_interval_nat_ladder_c08626 n (by omega) (by omega)
      · -- n <= 71043373567402497409
        rcases Nat.lt_or_ge 70524861073050106381 n with h8 | h8
        · -- n > 70524861073050106381
          rcases Nat.lt_or_ge 70697276529280667911 n with h10 | h10
          · -- n > 70697276529280667911
            rcases Nat.lt_or_ge 70870113650892638119 n with h12 | h12
            · -- n > 70870113650892638119
              exact RamareSaouter2003.prime_interval_nat_ladder_c08625 n (by omega) (by omega)
            · -- n <= 70870113650892638119
              exact RamareSaouter2003.prime_interval_nat_ladder_c08624 n (by omega) (by omega)
          · -- n <= 70697276529280667911
            exact RamareSaouter2003.prime_interval_nat_ladder_c08623 n (by omega) (by omega)
        · -- n <= 70524861073050106381
          rcases Nat.lt_or_ge 70181291356038389573 n with h10 | h10
          · -- n > 70181291356038389573
            rcases Nat.lt_or_ge 70352867249995165519 n with h12 | h12
            · -- n > 70352867249995165519
              exact RamareSaouter2003.prime_interval_nat_ladder_c08622 n (by omega) (by omega)
            · -- n <= 70352867249995165519
              exact RamareSaouter2003.prime_interval_nat_ladder_c08621 n (by omega) (by omega)
          · -- n <= 70181291356038389573
            exact RamareSaouter2003.prime_interval_nat_ladder_c08620 n (by omega) (by omega)
