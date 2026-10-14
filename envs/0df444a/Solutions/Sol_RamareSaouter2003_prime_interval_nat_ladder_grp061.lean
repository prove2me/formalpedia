-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp061
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T01:55:30.955251+00:00
-- url     : https://prove2.me/submissions/03b06381-83b1-4587-9890-29775bf3e160

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03050

theorem solution (n : Nat)
    (hn : 15174303375743 < n) (hupper : n <= 17170407053213) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 16141529224361 n with h2 | h2
  · -- n > 16141529224361
    rcases Nat.lt_or_ge 16627460146529 n with h4 | h4
    · -- n > 16627460146529
      rcases Nat.lt_or_ge 16875884135233 n with h6 | h6
      · -- n > 16875884135233
        rcases Nat.lt_or_ge 17001484532699 n with h8 | h8
        · -- n > 17001484532699
          rcases Nat.lt_or_ge 17085737032213 n with h10 | h10
          · -- n > 17085737032213
            rcases Nat.lt_or_ge 17128019723447 n with h12 | h12
            · -- n > 17128019723447
              exact RamareSaouter2003.prime_interval_nat_ladder_c03050 n (by omega) (by omega)
            · -- n <= 17128019723447
              exact RamareSaouter2003.prime_interval_nat_ladder_c03049 n (by omega) (by omega)
          · -- n <= 17085737032213
            rcases Nat.lt_or_ge 17043558721139 n with h12 | h12
            · -- n > 17043558721139
              exact RamareSaouter2003.prime_interval_nat_ladder_c03048 n (by omega) (by omega)
            · -- n <= 17043558721139
              exact RamareSaouter2003.prime_interval_nat_ladder_c03047 n (by omega) (by omega)
        · -- n <= 17001484532699
          rcases Nat.lt_or_ge 16917647495813 n with h10 | h10
          · -- n > 16917647495813
            rcases Nat.lt_or_ge 16959514209611 n with h12 | h12
            · -- n > 16959514209611
              exact RamareSaouter2003.prime_interval_nat_ladder_c03046 n (by omega) (by omega)
            · -- n <= 16959514209611
              exact RamareSaouter2003.prime_interval_nat_ladder_c03045 n (by omega) (by omega)
          · -- n <= 16917647495813
            exact RamareSaouter2003.prime_interval_nat_ladder_c03044 n (by omega) (by omega)
      · -- n <= 16875884135233
        rcases Nat.lt_or_ge 16751211624709 n with h8 | h8
        · -- n > 16751211624709
          rcases Nat.lt_or_ge 16792666453859 n with h10 | h10
          · -- n > 16792666453859
            rcases Nat.lt_or_ge 16834223872727 n with h12 | h12
            · -- n > 16834223872727
              exact RamareSaouter2003.prime_interval_nat_ladder_c03043 n (by omega) (by omega)
            · -- n <= 16834223872727
              exact RamareSaouter2003.prime_interval_nat_ladder_c03042 n (by omega) (by omega)
          · -- n <= 16792666453859
            exact RamareSaouter2003.prime_interval_nat_ladder_c03041 n (by omega) (by omega)
        · -- n <= 16751211624709
          rcases Nat.lt_or_ge 16668608723387 n with h10 | h10
          · -- n > 16668608723387
            rcases Nat.lt_or_ge 16709859132079 n with h12 | h12
            · -- n > 16709859132079
              exact RamareSaouter2003.prime_interval_nat_ladder_c03040 n (by omega) (by omega)
            · -- n <= 16709859132079
              exact RamareSaouter2003.prime_interval_nat_ladder_c03039 n (by omega) (by omega)
          · -- n <= 16668608723387
            exact RamareSaouter2003.prime_interval_nat_ladder_c03038 n (by omega) (by omega)
    · -- n <= 16627460146529
      rcases Nat.lt_or_ge 16382693120533 n with h6 | h6
      · -- n > 16382693120533
        rcases Nat.lt_or_ge 16504622896453 n with h8 | h8
        · -- n > 16504622896453
          rcases Nat.lt_or_ge 16545467483549 n with h10 | h10
          · -- n > 16545467483549
            rcases Nat.lt_or_ge 16586413150193 n with h12 | h12
            · -- n > 16586413150193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03037 n (by omega) (by omega)
            · -- n <= 16586413150193
              exact RamareSaouter2003.prime_interval_nat_ladder_c03036 n (by omega) (by omega)
          · -- n <= 16545467483549
            exact RamareSaouter2003.prime_interval_nat_ladder_c03035 n (by omega) (by omega)
        · -- n <= 16504622896453
          rcases Nat.lt_or_ge 16423235963593 n with h10 | h10
          · -- n > 16423235963593
            rcases Nat.lt_or_ge 16463879139439 n with h12 | h12
            · -- n > 16463879139439
              exact RamareSaouter2003.prime_interval_nat_ladder_c03034 n (by omega) (by omega)
            · -- n <= 16463879139439
              exact RamareSaouter2003.prime_interval_nat_ladder_c03033 n (by omega) (by omega)
          · -- n <= 16423235963593
            exact RamareSaouter2003.prime_interval_nat_ladder_c03032 n (by omega) (by omega)
      · -- n <= 16382693120533
        rcases Nat.lt_or_ge 16261664114671 n with h8 | h8
        · -- n > 16261664114671
          rcases Nat.lt_or_ge 16301907442901 n with h10 | h10
          · -- n > 16301907442901
            rcases Nat.lt_or_ge 16342250362657 n with h12 | h12
            · -- n > 16342250362657
              exact RamareSaouter2003.prime_interval_nat_ladder_c03031 n (by omega) (by omega)
            · -- n <= 16342250362657
              exact RamareSaouter2003.prime_interval_nat_ladder_c03030 n (by omega) (by omega)
          · -- n <= 16301907442901
            exact RamareSaouter2003.prime_interval_nat_ladder_c03029 n (by omega) (by omega)
        · -- n <= 16261664114671
          rcases Nat.lt_or_ge 16181475250379 n with h10 | h10
          · -- n > 16181475250379
            rcases Nat.lt_or_ge 16221520132241 n with h12 | h12
            · -- n > 16221520132241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03028 n (by omega) (by omega)
            · -- n <= 16221520132241
              exact RamareSaouter2003.prime_interval_nat_ladder_c03027 n (by omega) (by omega)
          · -- n <= 16181475250379
            exact RamareSaouter2003.prime_interval_nat_ladder_c03026 n (by omega) (by omega)
  · -- n <= 16141529224361
    rcases Nat.lt_or_ge 15631116551527 n with h4 | h4
    · -- n > 15631116551527
      rcases Nat.lt_or_ge 15864654583343 n with h6 | h6
      · -- n > 15864654583343
        rcases Nat.lt_or_ge 15982728807433 n with h8 | h8
        · -- n > 15982728807433
          rcases Nat.lt_or_ge 16061932764541 n with h10 | h10
          · -- n > 16061932764541
            rcases Nat.lt_or_ge 16101681810251 n with h12 | h12
            · -- n > 16101681810251
              exact RamareSaouter2003.prime_interval_nat_ladder_c03025 n (by omega) (by omega)
            · -- n <= 16101681810251
              exact RamareSaouter2003.prime_interval_nat_ladder_c03024 n (by omega) (by omega)
          · -- n <= 16061932764541
            rcases Nat.lt_or_ge 16022281844297 n with h12 | h12
            · -- n > 16022281844297
              exact RamareSaouter2003.prime_interval_nat_ladder_c03023 n (by omega) (by omega)
            · -- n <= 16022281844297
              exact RamareSaouter2003.prime_interval_nat_ladder_c03022 n (by omega) (by omega)
        · -- n <= 15982728807433
          rcases Nat.lt_or_ge 15903915417617 n with h10 | h10
          · -- n > 15903915417617
            rcases Nat.lt_or_ge 15943273412203 n with h12 | h12
            · -- n > 15943273412203
              exact RamareSaouter2003.prime_interval_nat_ladder_c03021 n (by omega) (by omega)
            · -- n <= 15943273412203
              exact RamareSaouter2003.prime_interval_nat_ladder_c03020 n (by omega) (by omega)
          · -- n <= 15903915417617
            exact RamareSaouter2003.prime_interval_nat_ladder_c03019 n (by omega) (by omega)
      · -- n <= 15864654583343
        rcases Nat.lt_or_ge 15747452646227 n with h8 | h8
        · -- n > 15747452646227
          rcases Nat.lt_or_ge 15786423436499 n with h10 | h10
          · -- n > 15786423436499
            rcases Nat.lt_or_ge 15825490669343 n with h12 | h12
            · -- n > 15825490669343
              exact RamareSaouter2003.prime_interval_nat_ladder_c03018 n (by omega) (by omega)
            · -- n <= 15825490669343
              exact RamareSaouter2003.prime_interval_nat_ladder_c03017 n (by omega) (by omega)
          · -- n <= 15786423436499
            exact RamareSaouter2003.prime_interval_nat_ladder_c03016 n (by omega) (by omega)
        · -- n <= 15747452646227
          rcases Nat.lt_or_ge 15669799440871 n with h10 | h10
          · -- n > 15669799440871
            rcases Nat.lt_or_ge 15708578060141 n with h12 | h12
            · -- n > 15708578060141
              exact RamareSaouter2003.prime_interval_nat_ladder_c03015 n (by omega) (by omega)
            · -- n <= 15708578060141
              exact RamareSaouter2003.prime_interval_nat_ladder_c03014 n (by omega) (by omega)
          · -- n <= 15669799440871
            exact RamareSaouter2003.prime_interval_nat_ladder_c03013 n (by omega) (by omega)
    · -- n <= 15631116551527
      rcases Nat.lt_or_ge 15401016351211 n with h6 | h6
      · -- n > 15401016351211
        rcases Nat.lt_or_ge 15515639902877 n with h8 | h8
        · -- n > 15515639902877
          rcases Nat.lt_or_ge 15554037017993 n with h10 | h10
          · -- n > 15554037017993
            rcases Nat.lt_or_ge 15592529155831 n with h12 | h12
            · -- n > 15592529155831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03012 n (by omega) (by omega)
            · -- n <= 15592529155831
              exact RamareSaouter2003.prime_interval_nat_ladder_c03011 n (by omega) (by omega)
          · -- n <= 15554037017993
            exact RamareSaouter2003.prime_interval_nat_ladder_c03010 n (by omega) (by omega)
        · -- n <= 15515639902877
          rcases Nat.lt_or_ge 15439129803217 n with h10 | h10
          · -- n > 15439129803217
            rcases Nat.lt_or_ge 15477337575961 n with h12 | h12
            · -- n > 15477337575961
              exact RamareSaouter2003.prime_interval_nat_ladder_c03009 n (by omega) (by omega)
            · -- n <= 15477337575961
              exact RamareSaouter2003.prime_interval_nat_ladder_c03008 n (by omega) (by omega)
          · -- n <= 15439129803217
            exact RamareSaouter2003.prime_interval_nat_ladder_c03007 n (by omega) (by omega)
      · -- n <= 15401016351211
        rcases Nat.lt_or_ge 15287239594247 n with h8 | h8
        · -- n > 15287239594247
          rcases Nat.lt_or_ge 15325071478627 n with h10 | h10
          · -- n > 15325071478627
            rcases Nat.lt_or_ge 15362996987077 n with h12 | h12
            · -- n > 15362996987077
              exact RamareSaouter2003.prime_interval_nat_ladder_c03006 n (by omega) (by omega)
            · -- n <= 15362996987077
              exact RamareSaouter2003.prime_interval_nat_ladder_c03005 n (by omega) (by omega)
          · -- n <= 15325071478627
            exact RamareSaouter2003.prime_interval_nat_ladder_c03004 n (by omega) (by omega)
        · -- n <= 15287239594247
          rcases Nat.lt_or_ge 15211855773019 n with h10 | h10
          · -- n > 15211855773019
            rcases Nat.lt_or_ge 15249501102571 n with h12 | h12
            · -- n > 15249501102571
              exact RamareSaouter2003.prime_interval_nat_ladder_c03003 n (by omega) (by omega)
            · -- n <= 15249501102571
              exact RamareSaouter2003.prime_interval_nat_ladder_c03002 n (by omega) (by omega)
          · -- n <= 15211855773019
            exact RamareSaouter2003.prime_interval_nat_ladder_c03001 n (by omega) (by omega)
