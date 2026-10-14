-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_sgrp1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T16:33:46.014552+00:00
-- url     : https://prove2.me/submissions/352bd42e-334d-4182-978b-8bfcc459be5d

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_grp044

theorem solution (n : Nat)
    (hn : 10726905041 < n) (hupper : n <= 2082320379773) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 129985561751 n with h2 | h2
  · -- n > 129985561751
    rcases Nat.lt_or_ge 516674572321 n with h4 | h4
    · -- n > 516674572321
      rcases Nat.lt_or_ge 973153707433 n with h6 | h6
      · -- n > 973153707433
        rcases Nat.lt_or_ge 1424081223991 n with h8 | h8
        · -- n > 1424081223991
          rcases Nat.lt_or_ge 1616505218459 n with h10 | h10
          · -- n > 1616505218459
            rcases Nat.lt_or_ge 1834768879973 n with h12 | h12
            · -- n > 1834768879973
              exact RamareSaouter2003.prime_interval_nat_ladder_grp044 n (by omega) (by omega)
            · -- n <= 1834768879973
              exact RamareSaouter2003.prime_interval_nat_ladder_grp043 n (by omega) (by omega)
          · -- n <= 1616505218459
            exact RamareSaouter2003.prime_interval_nat_ladder_grp042 n (by omega) (by omega)
        · -- n <= 1424081223991
          rcases Nat.lt_or_ge 1104932290381 n with h10 | h10
          · -- n > 1104932290381
            rcases Nat.lt_or_ge 1254452690677 n with h12 | h12
            · -- n > 1254452690677
              exact RamareSaouter2003.prime_interval_nat_ladder_grp041 n (by omega) (by omega)
            · -- n <= 1254452690677
              exact RamareSaouter2003.prime_interval_nat_ladder_grp040 n (by omega) (by omega)
          · -- n <= 1104932290381
            exact RamareSaouter2003.prime_interval_nat_ladder_grp039 n (by omega) (by omega)
      · -- n <= 973153707433
        rcases Nat.lt_or_ge 665289962371 n with h8 | h8
        · -- n > 665289962371
          rcases Nat.lt_or_ge 755098777861 n with h10 | h10
          · -- n > 755098777861
            rcases Nat.lt_or_ge 857157375181 n with h12 | h12
            · -- n > 857157375181
              exact RamareSaouter2003.prime_interval_nat_ladder_grp038 n (by omega) (by omega)
            · -- n <= 857157375181
              exact RamareSaouter2003.prime_interval_nat_ladder_grp037 n (by omega) (by omega)
          · -- n <= 755098777861
            exact RamareSaouter2003.prime_interval_nat_ladder_grp036 n (by omega) (by omega)
        · -- n <= 665289962371
          rcases Nat.lt_or_ge 586248983429 n with h10 | h10
          · -- n > 586248983429
            exact RamareSaouter2003.prime_interval_nat_ladder_grp035 n (by omega) (by omega)
          · -- n <= 586248983429
            exact RamareSaouter2003.prime_interval_nat_ladder_grp034 n (by omega) (by omega)
    · -- n <= 516674572321
      rcases Nat.lt_or_ge 242864356649 n with h6 | h6
      · -- n > 242864356649
        rcases Nat.lt_or_ge 354000949151 n with h8 | h8
        · -- n > 354000949151
          rcases Nat.lt_or_ge 401493320309 n with h10 | h10
          · -- n > 401493320309
            rcases Nat.lt_or_ge 455423937959 n with h12 | h12
            · -- n > 455423937959
              exact RamareSaouter2003.prime_interval_nat_ladder_grp033 n (by omega) (by omega)
            · -- n <= 455423937959
              exact RamareSaouter2003.prime_interval_nat_ladder_grp032 n (by omega) (by omega)
          · -- n <= 401493320309
            exact RamareSaouter2003.prime_interval_nat_ladder_grp031 n (by omega) (by omega)
        · -- n <= 354000949151
          rcases Nat.lt_or_ge 275326001903 n with h10 | h10
          · -- n > 275326001903
            rcases Nat.lt_or_ge 312172099721 n with h12 | h12
            · -- n > 312172099721
              exact RamareSaouter2003.prime_interval_nat_ladder_grp030 n (by omega) (by omega)
            · -- n <= 312172099721
              exact RamareSaouter2003.prime_interval_nat_ladder_grp029 n (by omega) (by omega)
          · -- n <= 275326001903
            exact RamareSaouter2003.prime_interval_nat_ladder_grp028 n (by omega) (by omega)
      · -- n <= 242864356649
        rcases Nat.lt_or_ge 166837303537 n with h8 | h8
        · -- n > 166837303537
          rcases Nat.lt_or_ge 189054413519 n with h10 | h10
          · -- n > 189054413519
            rcases Nat.lt_or_ge 214261267621 n with h12 | h12
            · -- n > 214261267621
              exact RamareSaouter2003.prime_interval_nat_ladder_grp027 n (by omega) (by omega)
            · -- n <= 214261267621
              exact RamareSaouter2003.prime_interval_nat_ladder_grp026 n (by omega) (by omega)
          · -- n <= 189054413519
            exact RamareSaouter2003.prime_interval_nat_ladder_grp025 n (by omega) (by omega)
        · -- n <= 166837303537
          rcases Nat.lt_or_ge 147252479863 n with h10 | h10
          · -- n > 147252479863
            exact RamareSaouter2003.prime_interval_nat_ladder_grp024 n (by omega) (by omega)
          · -- n <= 147252479863
            exact RamareSaouter2003.prime_interval_nat_ladder_grp023 n (by omega) (by omega)
  · -- n <= 129985561751
    rcases Nat.lt_or_ge 36137549639 n with h4 | h4
    · -- n > 36137549639
      rcases Nat.lt_or_ge 63861919811 n with h6 | h6
      · -- n > 63861919811
        rcases Nat.lt_or_ge 90188138827 n with h8 | h8
        · -- n > 90188138827
          rcases Nat.lt_or_ge 101332544893 n with h10 | h10
          · -- n > 101332544893
            rcases Nat.lt_or_ge 114760011811 n with h12 | h12
            · -- n > 114760011811
              exact RamareSaouter2003.prime_interval_nat_ladder_grp022 n (by omega) (by omega)
            · -- n <= 114760011811
              exact RamareSaouter2003.prime_interval_nat_ladder_grp021 n (by omega) (by omega)
          · -- n <= 101332544893
            exact RamareSaouter2003.prime_interval_nat_ladder_grp020 n (by omega) (by omega)
        · -- n <= 90188138827
          rcases Nat.lt_or_ge 71627919427 n with h10 | h10
          · -- n > 71627919427
            rcases Nat.lt_or_ge 80362118567 n with h12 | h12
            · -- n > 80362118567
              exact RamareSaouter2003.prime_interval_nat_ladder_grp019 n (by omega) (by omega)
            · -- n <= 80362118567
              exact RamareSaouter2003.prime_interval_nat_ladder_grp018 n (by omega) (by omega)
          · -- n <= 71627919427
            exact RamareSaouter2003.prime_interval_nat_ladder_grp017 n (by omega) (by omega)
      · -- n <= 63861919811
        rcases Nat.lt_or_ge 45340845131 n with h8 | h8
        · -- n > 45340845131
          rcases Nat.lt_or_ge 50809618939 n with h10 | h10
          · -- n > 50809618939
            rcases Nat.lt_or_ge 56954749447 n with h12 | h12
            · -- n > 56954749447
              exact RamareSaouter2003.prime_interval_nat_ladder_grp016 n (by omega) (by omega)
            · -- n <= 56954749447
              exact RamareSaouter2003.prime_interval_nat_ladder_grp015 n (by omega) (by omega)
          · -- n <= 50809618939
            exact RamareSaouter2003.prime_interval_nat_ladder_grp014 n (by omega) (by omega)
        · -- n <= 45340845131
          rcases Nat.lt_or_ge 40472556721 n with h10 | h10
          · -- n > 40472556721
            exact RamareSaouter2003.prime_interval_nat_ladder_grp013 n (by omega) (by omega)
          · -- n <= 40472556721
            exact RamareSaouter2003.prime_interval_nat_ladder_grp012 n (by omega) (by omega)
    · -- n <= 36137549639
      rcases Nat.lt_or_ge 18481081387 n with h6 | h6
      · -- n > 18481081387
        rcases Nat.lt_or_ge 25781257687 n with h8 | h8
        · -- n > 25781257687
          rcases Nat.lt_or_ge 28838600017 n with h10 | h10
          · -- n > 28838600017
            rcases Nat.lt_or_ge 32276278889 n with h12 | h12
            · -- n > 32276278889
              exact RamareSaouter2003.prime_interval_nat_ladder_grp011 n (by omega) (by omega)
            · -- n <= 32276278889
              exact RamareSaouter2003.prime_interval_nat_ladder_grp010 n (by omega) (by omega)
          · -- n <= 28838600017
            exact RamareSaouter2003.prime_interval_nat_ladder_grp009 n (by omega) (by omega)
        · -- n <= 25781257687
          rcases Nat.lt_or_ge 20638678393 n with h10 | h10
          · -- n > 20638678393
            rcases Nat.lt_or_ge 23060765993 n with h12 | h12
            · -- n > 23060765993
              exact RamareSaouter2003.prime_interval_nat_ladder_grp008 n (by omega) (by omega)
            · -- n <= 23060765993
              exact RamareSaouter2003.prime_interval_nat_ladder_grp007 n (by omega) (by omega)
          · -- n <= 20638678393
            exact RamareSaouter2003.prime_interval_nat_ladder_grp006 n (by omega) (by omega)
      · -- n <= 18481081387
        rcases Nat.lt_or_ge 13313012261 n with h8 | h8
        · -- n > 13313012261
          rcases Nat.lt_or_ge 14843139557 n with h10 | h10
          · -- n > 14843139557
            rcases Nat.lt_or_ge 16558044781 n with h12 | h12
            · -- n > 16558044781
              exact RamareSaouter2003.prime_interval_nat_ladder_grp005 n (by omega) (by omega)
            · -- n <= 16558044781
              exact RamareSaouter2003.prime_interval_nat_ladder_grp004 n (by omega) (by omega)
          · -- n <= 14843139557
            exact RamareSaouter2003.prime_interval_nat_ladder_grp003 n (by omega) (by omega)
        · -- n <= 13313012261
          rcases Nat.lt_or_ge 11947020167 n with h10 | h10
          · -- n > 11947020167
            exact RamareSaouter2003.prime_interval_nat_ladder_grp002 n (by omega) (by omega)
          · -- n <= 11947020167
            exact RamareSaouter2003.prime_interval_nat_ladder_grp001 n (by omega) (by omega)
