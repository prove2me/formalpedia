-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp151
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T07:34:43.780241+00:00
-- url     : https://prove2.me/submissions/636ca036-d633-4565-9dd3-d460010be076

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07493
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07494
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07495
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07496
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07497
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07498
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07499
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07500
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07501
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07502
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07503
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07504
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07505
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07506
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07507
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07508
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07509
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07510
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07511
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07512
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07513
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07514
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07515
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07516
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07517
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07518
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07519
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07520
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07521
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07522
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07523
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07524
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07525
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07526
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07527
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07528
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07529
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07530
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07531
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07532
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07533
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07534
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07535
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07536
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07537
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07538
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07539
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07540
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07541

theorem solution (n : Nat)
    (hn : 3570765072310602017 < n) (hupper : n <= 4101353957833713881) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 3821468867205849841 n with h2 | h2
  · -- n > 3821468867205849841
    rcases Nat.lt_or_ge 3953346116319915437 n with h4 | h4
    · -- n > 3953346116319915437
      rcases Nat.lt_or_ge 4020981807124572733 n with h6 | h6
      · -- n > 4020981807124572733
        rcases Nat.lt_or_ge 4055232366304911353 n with h8 | h8
        · -- n > 4055232366304911353
          rcases Nat.lt_or_ge 4078227994478000329 n with h10 | h10
          · -- n > 4078227994478000329
            rcases Nat.lt_or_ge 4089774594457727839 n with h12 | h12
            · -- n > 4089774594457727839
              exact RamareSaouter2003.prime_interval_nat_ladder_c07541 n (by omega) (by omega)
            · -- n <= 4089774594457727839
              exact RamareSaouter2003.prime_interval_nat_ladder_c07540 n (by omega) (by omega)
          · -- n <= 4078227994478000329
            rcases Nat.lt_or_ge 4066713914416472233 n with h12 | h12
            · -- n > 4066713914416472233
              exact RamareSaouter2003.prime_interval_nat_ladder_c07539 n (by omega) (by omega)
            · -- n <= 4066713914416472233
              exact RamareSaouter2003.prime_interval_nat_ladder_c07538 n (by omega) (by omega)
        · -- n <= 4055232366304911353
          rcases Nat.lt_or_ge 4032366385293322789 n with h10 | h10
          · -- n > 4032366385293322789
            rcases Nat.lt_or_ge 4043783196721318859 n with h12 | h12
            · -- n > 4043783196721318859
              exact RamareSaouter2003.prime_interval_nat_ladder_c07537 n (by omega) (by omega)
            · -- n <= 4043783196721318859
              exact RamareSaouter2003.prime_interval_nat_ladder_c07536 n (by omega) (by omega)
          · -- n <= 4032366385293322789
            exact RamareSaouter2003.prime_interval_nat_ladder_c07535 n (by omega) (by omega)
      · -- n <= 4020981807124572733
        rcases Nat.lt_or_ge 3987020570466092749 n with h8 | h8
        · -- n > 3987020570466092749
          rcases Nat.lt_or_ge 3998308997887248659 n with h10 | h10
          · -- n > 3998308997887248659
            rcases Nat.lt_or_ge 4009629321942830767 n with h12 | h12
            · -- n > 4009629321942830767
              exact RamareSaouter2003.prime_interval_nat_ladder_c07534 n (by omega) (by omega)
            · -- n <= 4009629321942830767
              exact RamareSaouter2003.prime_interval_nat_ladder_c07533 n (by omega) (by omega)
          · -- n <= 3998308997887248659
            exact RamareSaouter2003.prime_interval_nat_ladder_c07532 n (by omega) (by omega)
        · -- n <= 3987020570466092749
          rcases Nat.lt_or_ge 3964539145520737481 n with h10 | h10
          · -- n > 3964539145520737481
            rcases Nat.lt_or_ge 3975763961230107467 n with h12 | h12
            · -- n > 3975763961230107467
              exact RamareSaouter2003.prime_interval_nat_ladder_c07531 n (by omega) (by omega)
            · -- n <= 3975763961230107467
              exact RamareSaouter2003.prime_interval_nat_ladder_c07530 n (by omega) (by omega)
          · -- n <= 3964539145520737481
            exact RamareSaouter2003.prime_interval_nat_ladder_c07529 n (by omega) (by omega)
    · -- n <= 3953346116319915437
      rcases Nat.lt_or_ge 3886848294153990617 n with h6 | h6
      · -- n > 3886848294153990617
        rcases Nat.lt_or_ge 3919956339069847841 n with h8 | h8
        · -- n > 3919956339069847841
          rcases Nat.lt_or_ge 3931054853049577717 n with h10 | h10
          · -- n > 3931054853049577717
            rcases Nat.lt_or_ge 3942184591351507073 n with h12 | h12
            · -- n > 3942184591351507073
              exact RamareSaouter2003.prime_interval_nat_ladder_c07528 n (by omega) (by omega)
            · -- n <= 3942184591351507073
              exact RamareSaouter2003.prime_interval_nat_ladder_c07527 n (by omega) (by omega)
          · -- n <= 3931054853049577717
            exact RamareSaouter2003.prime_interval_nat_ladder_c07526 n (by omega) (by omega)
        · -- n <= 3919956339069847841
          rcases Nat.lt_or_ge 3897853074319405987 n with h10 | h10
          · -- n > 3897853074319405987
            rcases Nat.lt_or_ge 3908889089512930139 n with h12 | h12
            · -- n > 3908889089512930139
              exact RamareSaouter2003.prime_interval_nat_ladder_c07525 n (by omega) (by omega)
            · -- n <= 3908889089512930139
              exact RamareSaouter2003.prime_interval_nat_ladder_c07524 n (by omega) (by omega)
          · -- n <= 3897853074319405987
            exact RamareSaouter2003.prime_interval_nat_ladder_c07523 n (by omega) (by omega)
      · -- n <= 3886848294153990617
        rcases Nat.lt_or_ge 3854019975329661019 n with h8 | h8
        · -- n > 3854019975329661019
          rcases Nat.lt_or_ge 3864931855433976961 n with h10 | h10
          · -- n > 3864931855433976961
            rcases Nat.lt_or_ge 3875874647460515417 n with h12 | h12
            · -- n > 3875874647460515417
              exact RamareSaouter2003.prime_interval_nat_ladder_c07522 n (by omega) (by omega)
            · -- n <= 3875874647460515417
              exact RamareSaouter2003.prime_interval_nat_ladder_c07521 n (by omega) (by omega)
          · -- n <= 3864931855433976961
            exact RamareSaouter2003.prime_interval_nat_ladder_c07520 n (by omega) (by omega)
        · -- n <= 3854019975329661019
          rcases Nat.lt_or_ge 3832288530583691833 n with h10 | h10
          · -- n > 3832288530583691833
            rcases Nat.lt_or_ge 3843138882192514547 n with h12 | h12
            · -- n > 3843138882192514547
              exact RamareSaouter2003.prime_interval_nat_ladder_c07519 n (by omega) (by omega)
            · -- n <= 3843138882192514547
              exact RamareSaouter2003.prime_interval_nat_ladder_c07518 n (by omega) (by omega)
          · -- n <= 3832288530583691833
            exact RamareSaouter2003.prime_interval_nat_ladder_c07517 n (by omega) (by omega)
  · -- n <= 3821468867205849841
    rcases Nat.lt_or_ge 3693990827379184613 n with h4 | h4
    · -- n > 3693990827379184613
      rcases Nat.lt_or_ge 3757189074733535677 n with h6 | h6
      · -- n > 3757189074733535677
        rcases Nat.lt_or_ge 3789192782260672049 n with h8 | h8
        · -- n > 3789192782260672049
          rcases Nat.lt_or_ge 3799921039737453199 n with h10 | h10
          · -- n > 3799921039737453199
            rcases Nat.lt_or_ge 3810679709599179631 n with h12 | h12
            · -- n > 3810679709599179631
              exact RamareSaouter2003.prime_interval_nat_ladder_c07516 n (by omega) (by omega)
            · -- n <= 3810679709599179631
              exact RamareSaouter2003.prime_interval_nat_ladder_c07515 n (by omega) (by omega)
          · -- n <= 3799921039737453199
            exact RamareSaouter2003.prime_interval_nat_ladder_c07514 n (by omega) (by omega)
        · -- n <= 3789192782260672049
          rcases Nat.lt_or_ge 3767826828546850919 n with h10 | h10
          · -- n > 3767826828546850919
            rcases Nat.lt_or_ge 3778494704476040371 n with h12 | h12
            · -- n > 3778494704476040371
              exact RamareSaouter2003.prime_interval_nat_ladder_c07513 n (by omega) (by omega)
            · -- n <= 3778494704476040371
              exact RamareSaouter2003.prime_interval_nat_ladder_c07512 n (by omega) (by omega)
          · -- n <= 3767826828546850919
            exact RamareSaouter2003.prime_interval_nat_ladder_c07511 n (by omega) (by omega)
      · -- n <= 3757189074733535677
        rcases Nat.lt_or_ge 3725455815980717219 n with h8 | h8
        · -- n > 3725455815980717219
          rcases Nat.lt_or_ge 3736003697851175033 n with h10 | h10
          · -- n > 3736003697851175033
            rcases Nat.lt_or_ge 3746581394596659643 n with h12 | h12
            · -- n > 3746581394596659643
              exact RamareSaouter2003.prime_interval_nat_ladder_c07510 n (by omega) (by omega)
            · -- n <= 3746581394596659643
              exact RamareSaouter2003.prime_interval_nat_ladder_c07509 n (by omega) (by omega)
          · -- n <= 3736003697851175033
            exact RamareSaouter2003.prime_interval_nat_ladder_c07508 n (by omega) (by omega)
        · -- n <= 3725455815980717219
          rcases Nat.lt_or_ge 3704449592527837031 n with h10 | h10
          · -- n > 3704449592527837031
            rcases Nat.lt_or_ge 3714937848405194149 n with h12 | h12
            · -- n > 3714937848405194149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07507 n (by omega) (by omega)
            · -- n <= 3714937848405194149
              exact RamareSaouter2003.prime_interval_nat_ladder_c07506 n (by omega) (by omega)
          · -- n <= 3704449592527837031
            exact RamareSaouter2003.prime_interval_nat_ladder_c07505 n (by omega) (by omega)
    · -- n <= 3693990827379184613
      rcases Nat.lt_or_ge 3631855431089244077 n with h6 | h6
      · -- n > 3631855431089244077
        rcases Nat.lt_or_ge 3662791455418783801 n with h8 | h8
        · -- n > 3662791455418783801
          rcases Nat.lt_or_ge 3673161905970365951 n with h10 | h10
          · -- n > 3673161905970365951
            rcases Nat.lt_or_ge 3683561729856932201 n with h12 | h12
            · -- n > 3683561729856932201
              exact RamareSaouter2003.prime_interval_nat_ladder_c07504 n (by omega) (by omega)
            · -- n <= 3683561729856932201
              exact RamareSaouter2003.prime_interval_nat_ladder_c07503 n (by omega) (by omega)
          · -- n <= 3673161905970365951
            exact RamareSaouter2003.prime_interval_nat_ladder_c07502 n (by omega) (by omega)
        · -- n <= 3662791455418783801
          rcases Nat.lt_or_ge 3642138253203282803 n with h10 | h10
          · -- n > 3642138253203282803
            rcases Nat.lt_or_ge 3652450258268085061 n with h12 | h12
            · -- n > 3652450258268085061
              exact RamareSaouter2003.prime_interval_nat_ladder_c07501 n (by omega) (by omega)
            · -- n <= 3652450258268085061
              exact RamareSaouter2003.prime_interval_nat_ladder_c07500 n (by omega) (by omega)
          · -- n <= 3642138253203282803
            exact RamareSaouter2003.prime_interval_nat_ladder_c07499 n (by omega) (by omega)
      · -- n <= 3631855431089244077
        rcases Nat.lt_or_ge 3601180673998905677 n with h8 | h8
        · -- n > 3601180673998905677
          rcases Nat.lt_or_ge 3611376723584172703 n with h10 | h10
          · -- n > 3611376723584172703
            rcases Nat.lt_or_ge 3621601570184454917 n with h12 | h12
            · -- n > 3621601570184454917
              exact RamareSaouter2003.prime_interval_nat_ladder_c07498 n (by omega) (by omega)
            · -- n <= 3621601570184454917
              exact RamareSaouter2003.prime_interval_nat_ladder_c07497 n (by omega) (by omega)
          · -- n <= 3611376723584172703
            exact RamareSaouter2003.prime_interval_nat_ladder_c07496 n (by omega) (by omega)
        · -- n <= 3601180673998905677
          rcases Nat.lt_or_ge 3580874971542751217 n with h10 | h10
          · -- n > 3580874971542751217
            rcases Nat.lt_or_ge 3591013466299643983 n with h12 | h12
            · -- n > 3591013466299643983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07495 n (by omega) (by omega)
            · -- n <= 3591013466299643983
              exact RamareSaouter2003.prime_interval_nat_ladder_c07494 n (by omega) (by omega)
          · -- n <= 3580874971542751217
            exact RamareSaouter2003.prime_interval_nat_ladder_c07493 n (by omega) (by omega)
