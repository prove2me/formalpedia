-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp155
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T09:09:23.434184+00:00
-- url     : https://prove2.me/submissions/743a9081-b5c4-499a-aaf8-10dab48c64b3

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07689
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07690
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07691
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07692
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07693
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07694
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07695
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07696
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07697
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07698
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07699
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07700
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07701
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07702
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07703
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07704
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07705
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07706
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07707
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07708
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07709
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07710
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07711
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07712
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07713
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07714
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07715
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07716
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07717
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07718
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07719
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07720
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07721
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07722
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07723
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07724
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07725
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07726
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07727
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07728
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07729
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07730
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07731
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07732
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07733
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07734
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07735
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07736
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07737

theorem solution (n : Nat)
    (hn : 6214769977508183639 < n) (hupper : n <= 7138238304410545217) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 6651109566590166611 n with h2 | h2
  · -- n > 6651109566590166611
    rcases Nat.lt_or_ge 6880636784957958961 n with h4 | h4
    · -- n > 6880636784957958961
      rcases Nat.lt_or_ge 6998353947777573883 n with h6 | h6
      · -- n > 6998353947777573883
        rcases Nat.lt_or_ge 7057965591887768431 n with h8 | h8
        · -- n > 7057965591887768431
          rcases Nat.lt_or_ge 7097988371408172649 n with h10 | h10
          · -- n > 7097988371408172649
            rcases Nat.lt_or_ge 7118084903512041359 n with h12 | h12
            · -- n > 7118084903512041359
              exact RamareSaouter2003.prime_interval_nat_ladder_c07737 n (by omega) (by omega)
            · -- n <= 7118084903512041359
              exact RamareSaouter2003.prime_interval_nat_ladder_c07736 n (by omega) (by omega)
          · -- n <= 7097988371408172649
            rcases Nat.lt_or_ge 7077948779083996259 n with h12 | h12
            · -- n > 7077948779083996259
              exact RamareSaouter2003.prime_interval_nat_ladder_c07735 n (by omega) (by omega)
            · -- n <= 7077948779083996259
              exact RamareSaouter2003.prime_interval_nat_ladder_c07734 n (by omega) (by omega)
        · -- n <= 7057965591887768431
          rcases Nat.lt_or_ge 7018168372092825967 n with h10 | h10
          · -- n > 7018168372092825967
            rcases Nat.lt_or_ge 7038038758481889797 n with h12 | h12
            · -- n > 7038038758481889797
              exact RamareSaouter2003.prime_interval_nat_ladder_c07733 n (by omega) (by omega)
            · -- n <= 7038038758481889797
              exact RamareSaouter2003.prime_interval_nat_ladder_c07732 n (by omega) (by omega)
          · -- n <= 7018168372092825967
            exact RamareSaouter2003.prime_interval_nat_ladder_c07731 n (by omega) (by omega)
      · -- n <= 6998353947777573883
        rcases Nat.lt_or_ge 6939245674368331459 n with h8 | h8
        · -- n > 6939245674368331459
          rcases Nat.lt_or_ge 6958892732811352117 n with h10 | h10
          · -- n > 6958892732811352117
            rcases Nat.lt_or_ge 6978595440617484517 n with h12 | h12
            · -- n > 6978595440617484517
              exact RamareSaouter2003.prime_interval_nat_ladder_c07730 n (by omega) (by omega)
            · -- n <= 6978595440617484517
              exact RamareSaouter2003.prime_interval_nat_ladder_c07729 n (by omega) (by omega)
          · -- n <= 6958892732811352117
            exact RamareSaouter2003.prime_interval_nat_ladder_c07728 n (by omega) (by omega)
        · -- n <= 6939245674368331459
          rcases Nat.lt_or_ge 6900117712639341731 n with h10 | h10
          · -- n > 6900117712639341731
            rcases Nat.lt_or_ge 6919654057722733693 n with h12 | h12
            · -- n > 6919654057722733693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07727 n (by omega) (by omega)
            · -- n <= 6919654057722733693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07726 n (by omega) (by omega)
          · -- n <= 6900117712639341731
            exact RamareSaouter2003.prime_interval_nat_ladder_c07725 n (by omega) (by omega)
    · -- n <= 6880636784957958961
      rcases Nat.lt_or_ge 6764899868416829143 n with h6 | h6
      · -- n > 6764899868416829143
        rcases Nat.lt_or_ge 6822522917604061069 n with h8 | h8
        · -- n > 6822522917604061069
          rcases Nat.lt_or_ge 6841839532187102089 n with h10 | h10
          · -- n > 6841839532187102089
            rcases Nat.lt_or_ge 6861210805467385483 n with h12 | h12
            · -- n > 6861210805467385483
              exact RamareSaouter2003.prime_interval_nat_ladder_c07724 n (by omega) (by omega)
            · -- n <= 6861210805467385483
              exact RamareSaouter2003.prime_interval_nat_ladder_c07723 n (by omega) (by omega)
          · -- n <= 6841839532187102089
            exact RamareSaouter2003.prime_interval_nat_ladder_c07722 n (by omega) (by omega)
        · -- n <= 6822522917604061069
          rcases Nat.lt_or_ge 6784053279248951633 n with h10 | h10
          · -- n > 6784053279248951633
            rcases Nat.lt_or_ge 6803260835230711769 n with h12 | h12
            · -- n > 6803260835230711769
              exact RamareSaouter2003.prime_interval_nat_ladder_c07721 n (by omega) (by omega)
            · -- n <= 6803260835230711769
              exact RamareSaouter2003.prime_interval_nat_ladder_c07720 n (by omega) (by omega)
          · -- n <= 6784053279248951633
            exact RamareSaouter2003.prime_interval_nat_ladder_c07719 n (by omega) (by omega)
      · -- n <= 6764899868416829143
        rcases Nat.lt_or_ge 6707763418570995149 n with h8 | h8
        · -- n > 6707763418570995149
          rcases Nat.lt_or_ge 6726754966656306773 n with h10 | h10
          · -- n > 6726754966656306773
            rcases Nat.lt_or_ge 6745800451482742163 n with h12 | h12
            · -- n > 6745800451482742163
              exact RamareSaouter2003.prime_interval_nat_ladder_c07718 n (by omega) (by omega)
            · -- n <= 6745800451482742163
              exact RamareSaouter2003.prime_interval_nat_ladder_c07717 n (by omega) (by omega)
          · -- n <= 6726754966656306773
            exact RamareSaouter2003.prime_interval_nat_ladder_c07716 n (by omega) (by omega)
        · -- n <= 6707763418570995149
          rcases Nat.lt_or_ge 6669940707078839167 n with h10 | h10
          · -- n > 6669940707078839167
            rcases Nat.lt_or_ge 6688825340510632079 n with h12 | h12
            · -- n > 6688825340510632079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07715 n (by omega) (by omega)
            · -- n <= 6688825340510632079
              exact RamareSaouter2003.prime_interval_nat_ladder_c07714 n (by omega) (by omega)
          · -- n <= 6669940707078839167
            exact RamareSaouter2003.prime_interval_nat_ladder_c07713 n (by omega) (by omega)
  · -- n <= 6651109566590166611
    rcases Nat.lt_or_ge 6429238919813887013 n with h4 | h4
    · -- n > 6429238919813887013
      rcases Nat.lt_or_ge 6539233707908839127 n with h6 | h6
      · -- n > 6539233707908839127
        rcases Nat.lt_or_ge 6594934643307452633 n with h8 | h8
        · -- n > 6594934643307452633
          rcases Nat.lt_or_ge 6613606615850975777 n with h10 | h10
          · -- n > 6613606615850975777
            rcases Nat.lt_or_ge 6632331504920248051 n with h12 | h12
            · -- n > 6632331504920248051
              exact RamareSaouter2003.prime_interval_nat_ladder_c07712 n (by omega) (by omega)
            · -- n <= 6632331504920248051
              exact RamareSaouter2003.prime_interval_nat_ladder_c07711 n (by omega) (by omega)
          · -- n <= 6613606615850975777
            exact RamareSaouter2003.prime_interval_nat_ladder_c07710 n (by omega) (by omega)
        · -- n <= 6594934643307452633
          rcases Nat.lt_or_ge 6557748161786265629 n with h10 | h10
          · -- n > 6557748161786265629
            rcases Nat.lt_or_ge 6576315140665191443 n with h12 | h12
            · -- n > 6576315140665191443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07709 n (by omega) (by omega)
            · -- n <= 6576315140665191443
              exact RamareSaouter2003.prime_interval_nat_ladder_c07708 n (by omega) (by omega)
          · -- n <= 6557748161786265629
            exact RamareSaouter2003.prime_interval_nat_ladder_c07707 n (by omega) (by omega)
      · -- n <= 6539233707908839127
        rcases Nat.lt_or_ge 6484003067109282829 n with h8 | h8
        · -- n > 6484003067109282829
          rcases Nat.lt_or_ge 6502361260351893479 n with h10 | h10
          · -- n > 6502361260351893479
            rcases Nat.lt_or_ge 6520771406712234391 n with h12 | h12
            · -- n > 6520771406712234391
              exact RamareSaouter2003.prime_interval_nat_ladder_c07706 n (by omega) (by omega)
            · -- n <= 6520771406712234391
              exact RamareSaouter2003.prime_interval_nat_ladder_c07705 n (by omega) (by omega)
          · -- n <= 6502361260351893479
            exact RamareSaouter2003.prime_interval_nat_ladder_c07704 n (by omega) (by omega)
        · -- n <= 6484003067109282829
          rcases Nat.lt_or_ge 6447442062306708343 n with h10 | h10
          · -- n > 6447442062306708343
            rcases Nat.lt_or_ge 6465696710823569507 n with h12 | h12
            · -- n > 6465696710823569507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07703 n (by omega) (by omega)
            · -- n <= 6465696710823569507
              exact RamareSaouter2003.prime_interval_nat_ladder_c07702 n (by omega) (by omega)
          · -- n <= 6447442062306708343
            exact RamareSaouter2003.prime_interval_nat_ladder_c07701 n (by omega) (by omega)
    · -- n <= 6429238919813887013
      rcases Nat.lt_or_ge 6321094965621896981 n with h6 | h6
      · -- n > 6321094965621896981
        rcases Nat.lt_or_ge 6374937896097164323 n with h8 | h8
        · -- n > 6374937896097164323
          rcases Nat.lt_or_ge 6392987052160677517 n with h10 | h10
          · -- n > 6392987052160677517
            rcases Nat.lt_or_ge 6411087372401035361 n with h12 | h12
            · -- n > 6411087372401035361
              exact RamareSaouter2003.prime_interval_nat_ladder_c07700 n (by omega) (by omega)
            · -- n <= 6411087372401035361
              exact RamareSaouter2003.prime_interval_nat_ladder_c07699 n (by omega) (by omega)
          · -- n <= 6392987052160677517
            exact RamareSaouter2003.prime_interval_nat_ladder_c07698 n (by omega) (by omega)
        · -- n <= 6374937896097164323
          rcases Nat.lt_or_ge 6338991877074696239 n with h10 | h10
          · -- n > 6338991877074696239
            rcases Nat.lt_or_ge 6356939493124121789 n with h12 | h12
            · -- n > 6356939493124121789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07697 n (by omega) (by omega)
            · -- n <= 6356939493124121789
              exact RamareSaouter2003.prime_interval_nat_ladder_c07696 n (by omega) (by omega)
          · -- n <= 6338991877074696239
            exact RamareSaouter2003.prime_interval_nat_ladder_c07695 n (by omega) (by omega)
      · -- n <= 6321094965621896981
        rcases Nat.lt_or_ge 6267706842752592511 n with h8 | h8
        · -- n > 6267706842752592511
          rcases Nat.lt_or_ge 6285452645585742619 n with h10 | h10
          · -- n > 6285452645585742619
            rcases Nat.lt_or_ge 6303248565644283599 n with h12 | h12
            · -- n > 6303248565644283599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07694 n (by omega) (by omega)
            · -- n <= 6303248565644283599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07693 n (by omega) (by omega)
          · -- n <= 6285452645585742619
            exact RamareSaouter2003.prime_interval_nat_ladder_c07692 n (by omega) (by omega)
        · -- n <= 6267706842752592511
          rcases Nat.lt_or_ge 6232365599889626279 n with h10 | h10
          · -- n > 6232365599889626279
            rcases Nat.lt_or_ge 6250011211334992979 n with h12 | h12
            · -- n > 6250011211334992979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07691 n (by omega) (by omega)
            · -- n <= 6250011211334992979
              exact RamareSaouter2003.prime_interval_nat_ladder_c07690 n (by omega) (by omega)
          · -- n <= 6232365599889626279
            exact RamareSaouter2003.prime_interval_nat_ladder_c07689 n (by omega) (by omega)
