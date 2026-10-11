-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp001
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T13:16:19.450927+00:00
-- url     : https://prove2.me/submissions/d8b55a49-5d8b-4054-baa3-b58bdc27ed9c

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00050

theorem solution (n : Nat)
    (hn : 10726905041 < n) (hupper : n <= 11947020167) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 11319784031 n with h2 | h2
  · -- n > 11319784031
    rcases Nat.lt_or_ge 11616444551 n with h4 | h4
    · -- n > 11616444551
      rcases Nat.lt_or_ge 11767813033 n with h6 | h6
      · -- n > 11767813033
        rcases Nat.lt_or_ge 11844269413 n with h8 | h8
        · -- n > 11844269413
          rcases Nat.lt_or_ge 11895528761 n with h10 | h10
          · -- n > 11895528761
            rcases Nat.lt_or_ge 11921245379 n with h12 | h12
            · -- n > 11921245379
              exact RamareSaouter2003.prime_interval_nat_ladder_c00050 n (by omega) (by omega)
            · -- n <= 11921245379
              exact RamareSaouter2003.prime_interval_nat_ladder_c00049 n (by omega) (by omega)
          · -- n <= 11895528761
            rcases Nat.lt_or_ge 11869870157 n with h12 | h12
            · -- n > 11869870157
              exact RamareSaouter2003.prime_interval_nat_ladder_c00048 n (by omega) (by omega)
            · -- n <= 11869870157
              exact RamareSaouter2003.prime_interval_nat_ladder_c00047 n (by omega) (by omega)
        · -- n <= 11844269413
          rcases Nat.lt_or_ge 11793240971 n with h10 | h10
          · -- n > 11793240971
            rcases Nat.lt_or_ge 11818726397 n with h12 | h12
            · -- n > 11818726397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00046 n (by omega) (by omega)
            · -- n <= 11818726397
              exact RamareSaouter2003.prime_interval_nat_ladder_c00045 n (by omega) (by omega)
          · -- n <= 11793240971
            exact RamareSaouter2003.prime_interval_nat_ladder_c00044 n (by omega) (by omega)
      · -- n <= 11767813033
        rcases Nat.lt_or_ge 11691872657 n with h8 | h8
        · -- n > 11691872657
          rcases Nat.lt_or_ge 11717129051 n with h10 | h10
          · -- n > 11717129051
            rcases Nat.lt_or_ge 11742442427 n with h12 | h12
            · -- n > 11742442427
              exact RamareSaouter2003.prime_interval_nat_ladder_c00043 n (by omega) (by omega)
            · -- n <= 11742442427
              exact RamareSaouter2003.prime_interval_nat_ladder_c00042 n (by omega) (by omega)
          · -- n <= 11717129051
            exact RamareSaouter2003.prime_interval_nat_ladder_c00041 n (by omega) (by omega)
        · -- n <= 11691872657
          rcases Nat.lt_or_ge 11641530553 n with h10 | h10
          · -- n > 11641530553
            rcases Nat.lt_or_ge 11666673199 n with h12 | h12
            · -- n > 11666673199
              exact RamareSaouter2003.prime_interval_nat_ladder_c00040 n (by omega) (by omega)
            · -- n <= 11666673199
              exact RamareSaouter2003.prime_interval_nat_ladder_c00039 n (by omega) (by omega)
          · -- n <= 11641530553
            exact RamareSaouter2003.prime_interval_nat_ladder_c00038 n (by omega) (by omega)
    · -- n <= 11616444551
      rcases Nat.lt_or_ge 11467111027 n with h6 | h6
      · -- n > 11467111027
        rcases Nat.lt_or_ge 11541525239 n with h8 | h8
        · -- n > 11541525239
          rcases Nat.lt_or_ge 11566442077 n with h10 | h10
          · -- n > 11566442077
            rcases Nat.lt_or_ge 11591415151 n with h12 | h12
            · -- n > 11591415151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00037 n (by omega) (by omega)
            · -- n <= 11591415151
              exact RamareSaouter2003.prime_interval_nat_ladder_c00036 n (by omega) (by omega)
          · -- n <= 11566442077
            exact RamareSaouter2003.prime_interval_nat_ladder_c00035 n (by omega) (by omega)
        · -- n <= 11541525239
          rcases Nat.lt_or_ge 11491859857 n with h10 | h10
          · -- n > 11491859857
            rcases Nat.lt_or_ge 11516664547 n with h12 | h12
            · -- n > 11516664547
              exact RamareSaouter2003.prime_interval_nat_ladder_c00034 n (by omega) (by omega)
            · -- n <= 11516664547
              exact RamareSaouter2003.prime_interval_nat_ladder_c00033 n (by omega) (by omega)
          · -- n <= 11491859857
            exact RamareSaouter2003.prime_interval_nat_ladder_c00032 n (by omega) (by omega)
      · -- n <= 11467111027
        rcases Nat.lt_or_ge 11393198507 n with h8 | h8
        · -- n > 11393198507
          rcases Nat.lt_or_ge 11417780483 n with h10 | h10
          · -- n > 11417780483
            rcases Nat.lt_or_ge 11442417941 n with h12 | h12
            · -- n > 11442417941
              exact RamareSaouter2003.prime_interval_nat_ladder_c00031 n (by omega) (by omega)
            · -- n <= 11442417941
              exact RamareSaouter2003.prime_interval_nat_ladder_c00030 n (by omega) (by omega)
          · -- n <= 11417780483
            exact RamareSaouter2003.prime_interval_nat_ladder_c00029 n (by omega) (by omega)
        · -- n <= 11393198507
          rcases Nat.lt_or_ge 11344200409 n with h10 | h10
          · -- n > 11344200409
            rcases Nat.lt_or_ge 11368671871 n with h12 | h12
            · -- n > 11368671871
              exact RamareSaouter2003.prime_interval_nat_ladder_c00028 n (by omega) (by omega)
            · -- n <= 11368671871
              exact RamareSaouter2003.prime_interval_nat_ladder_c00027 n (by omega) (by omega)
          · -- n <= 11344200409
            exact RamareSaouter2003.prime_interval_nat_ladder_c00026 n (by omega) (by omega)
  · -- n <= 11319784031
    rcases Nat.lt_or_ge 11007325783 n with h4 | h4
    · -- n > 11007325783
      rcases Nat.lt_or_ge 11150401057 n with h6 | h6
      · -- n > 11150401057
        rcases Nat.lt_or_ge 11222666849 n with h8 | h8
        · -- n > 11222666849
          rcases Nat.lt_or_ge 11271116053 n with h10 | h10
          · -- n > 11271116053
            rcases Nat.lt_or_ge 11295422647 n with h12 | h12
            · -- n > 11295422647
              exact RamareSaouter2003.prime_interval_nat_ladder_c00025 n (by omega) (by omega)
            · -- n <= 11295422647
              exact RamareSaouter2003.prime_interval_nat_ladder_c00024 n (by omega) (by omega)
          · -- n <= 11271116053
            rcases Nat.lt_or_ge 11246864179 n with h12 | h12
            · -- n > 11246864179
              exact RamareSaouter2003.prime_interval_nat_ladder_c00023 n (by omega) (by omega)
            · -- n <= 11246864179
              exact RamareSaouter2003.prime_interval_nat_ladder_c00022 n (by omega) (by omega)
        · -- n <= 11222666849
          rcases Nat.lt_or_ge 11174435423 n with h10 | h10
          · -- n > 11174435423
            rcases Nat.lt_or_ge 11198524003 n with h12 | h12
            · -- n > 11198524003
              exact RamareSaouter2003.prime_interval_nat_ladder_c00021 n (by omega) (by omega)
            · -- n <= 11198524003
              exact RamareSaouter2003.prime_interval_nat_ladder_c00020 n (by omega) (by omega)
          · -- n <= 11174435423
            exact RamareSaouter2003.prime_interval_nat_ladder_c00019 n (by omega) (by omega)
      · -- n <= 11150401057
        rcases Nat.lt_or_ge 11078621929 n with h8 | h8
        · -- n > 11078621929
          rcases Nat.lt_or_ge 11102494493 n with h10 | h10
          · -- n > 11102494493
            rcases Nat.lt_or_ge 11126420759 n with h12 | h12
            · -- n > 11126420759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00018 n (by omega) (by omega)
            · -- n <= 11126420759
              exact RamareSaouter2003.prime_interval_nat_ladder_c00017 n (by omega) (by omega)
          · -- n <= 11102494493
            exact RamareSaouter2003.prime_interval_nat_ladder_c00016 n (by omega) (by omega)
        · -- n <= 11078621929
          rcases Nat.lt_or_ge 11031037709 n with h10 | h10
          · -- n > 11031037709
            rcases Nat.lt_or_ge 11054803013 n with h12 | h12
            · -- n > 11054803013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00015 n (by omega) (by omega)
            · -- n <= 11054803013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00014 n (by omega) (by omega)
          · -- n <= 11031037709
            exact RamareSaouter2003.prime_interval_nat_ladder_c00013 n (by omega) (by omega)
    · -- n <= 11007325783
      rcases Nat.lt_or_ge 10866169333 n with h6 | h6
      · -- n > 10866169333
        rcases Nat.lt_or_ge 10936509413 n with h8 | h8
        · -- n > 10936509413
          rcases Nat.lt_or_ge 10960061747 n with h10 | h10
          · -- n > 10960061747
            rcases Nat.lt_or_ge 10983667169 n with h12 | h12
            · -- n > 10983667169
              exact RamareSaouter2003.prime_interval_nat_ladder_c00012 n (by omega) (by omega)
            · -- n <= 10983667169
              exact RamareSaouter2003.prime_interval_nat_ladder_c00011 n (by omega) (by omega)
          · -- n <= 10960061747
            exact RamareSaouter2003.prime_interval_nat_ladder_c00010 n (by omega) (by omega)
        · -- n <= 10936509413
          rcases Nat.lt_or_ge 10889563313 n with h10 | h10
          · -- n > 10889563313
            rcases Nat.lt_or_ge 10913009963 n with h12 | h12
            · -- n > 10913009963
              exact RamareSaouter2003.prime_interval_nat_ladder_c00009 n (by omega) (by omega)
            · -- n <= 10913009963
              exact RamareSaouter2003.prime_interval_nat_ladder_c00008 n (by omega) (by omega)
          · -- n <= 10889563313
            exact RamareSaouter2003.prime_interval_nat_ladder_c00007 n (by omega) (by omega)
      · -- n <= 10866169333
        rcases Nat.lt_or_ge 10796302291 n with h8 | h8
        · -- n > 10796302291
          rcases Nat.lt_or_ge 10819538963 n with h10 | h10
          · -- n > 10819538963
            rcases Nat.lt_or_ge 10842827921 n with h12 | h12
            · -- n > 10842827921
              exact RamareSaouter2003.prime_interval_nat_ladder_c00006 n (by omega) (by omega)
            · -- n <= 10842827921
              exact RamareSaouter2003.prime_interval_nat_ladder_c00005 n (by omega) (by omega)
          · -- n <= 10819538963
            exact RamareSaouter2003.prime_interval_nat_ladder_c00004 n (by omega) (by omega)
        · -- n <= 10796302291
          rcases Nat.lt_or_ge 10749985501 n with h10 | h10
          · -- n > 10749985501
            rcases Nat.lt_or_ge 10773117877 n with h12 | h12
            · -- n > 10773117877
              exact RamareSaouter2003.prime_interval_nat_ladder_c00003 n (by omega) (by omega)
            · -- n <= 10773117877
              exact RamareSaouter2003.prime_interval_nat_ladder_c00002 n (by omega) (by omega)
          · -- n <= 10749985501
            exact RamareSaouter2003.prime_interval_nat_ladder_c00001 n (by omega) (by omega)
