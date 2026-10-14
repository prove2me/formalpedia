-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T04:25:26.084116+00:00
-- url     : https://prove2.me/submissions/5ff0aea6-f0c9-4c74-8aba-6b7b5c3358c4

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07001
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07002
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07003
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07004
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07005
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07006
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07007
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07008
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07009
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07010
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07011
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07012
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07013
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07014
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07015
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07016
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07017
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07018
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07019
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07020
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07021
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07022
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07023
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07024
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07025
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07026
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07027
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07028
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07029
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07030
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07031
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07032
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07033
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07034
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07035
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07036
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07037
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07038
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07039
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07040
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07041
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07042
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07043
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07044
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07045
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07046
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07047
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07048
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07049
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07050

theorem solution (n : Nat)
    (hn : 888481536827254001 < n) (hupper : n <= 1023391151980165547) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 953553629797611407 n with h2 | h2
  · -- n > 953553629797611407
    rcases Nat.lt_or_ge 986459732597779217 n with h4 | h4
    · -- n > 986459732597779217
      rcases Nat.lt_or_ge 1003336395009361117 n with h6 | h6
      · -- n > 1003336395009361117
        rcases Nat.lt_or_ge 1011882767536212133 n with h8 | h8
        · -- n > 1011882767536212133
          rcases Nat.lt_or_ge 1017620721023875963 n with h10 | h10
          · -- n > 1017620721023875963
            rcases Nat.lt_or_ge 1020501884921472511 n with h12 | h12
            · -- n > 1020501884921472511
              exact RamareSaouter2003.prime_interval_nat_ladder_c07050 n (by omega) (by omega)
            · -- n <= 1020501884921472511
              exact RamareSaouter2003.prime_interval_nat_ladder_c07049 n (by omega) (by omega)
          · -- n <= 1017620721023875963
            rcases Nat.lt_or_ge 1014747711852089993 n with h12 | h12
            · -- n > 1014747711852089993
              exact RamareSaouter2003.prime_interval_nat_ladder_c07048 n (by omega) (by omega)
            · -- n <= 1014747711852089993
              exact RamareSaouter2003.prime_interval_nat_ladder_c07047 n (by omega) (by omega)
        · -- n <= 1011882767536212133
          rcases Nat.lt_or_ge 1006177142367918473 n with h10 | h10
          · -- n > 1006177142367918473
            rcases Nat.lt_or_ge 1009025915490581419 n with h12 | h12
            · -- n > 1009025915490581419
              exact RamareSaouter2003.prime_interval_nat_ladder_c07046 n (by omega) (by omega)
            · -- n <= 1009025915490581419
              exact RamareSaouter2003.prime_interval_nat_ladder_c07045 n (by omega) (by omega)
          · -- n <= 1006177142367918473
            exact RamareSaouter2003.prime_interval_nat_ladder_c07044 n (by omega) (by omega)
      · -- n <= 1003336395009361117
        rcases Nat.lt_or_ge 994862355713531519 n with h8 | h8
        · -- n > 994862355713531519
          rcases Nat.lt_or_ge 997679115652198321 n with h10 | h10
          · -- n > 997679115652198321
            rcases Nat.lt_or_ge 1000503674488476451 n with h12 | h12
            · -- n > 1000503674488476451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07043 n (by omega) (by omega)
            · -- n <= 1000503674488476451
              exact RamareSaouter2003.prime_interval_nat_ladder_c07042 n (by omega) (by omega)
          · -- n <= 997679115652198321
            exact RamareSaouter2003.prime_interval_nat_ladder_c07041 n (by omega) (by omega)
        · -- n <= 994862355713531519
          rcases Nat.lt_or_ge 989252690923254281 n with h10 | h10
          · -- n > 989252690923254281
            rcases Nat.lt_or_ge 992053563735813287 n with h12 | h12
            · -- n > 992053563735813287
              exact RamareSaouter2003.prime_interval_nat_ladder_c07040 n (by omega) (by omega)
            · -- n <= 992053563735813287
              exact RamareSaouter2003.prime_interval_nat_ladder_c07039 n (by omega) (by omega)
          · -- n <= 989252690923254281
            exact RamareSaouter2003.prime_interval_nat_ladder_c07038 n (by omega) (by omega)
    · -- n <= 986459732597779217
      rcases Nat.lt_or_ge 969867175623724759 n with h6 | h6
      · -- n > 969867175623724759
        rcases Nat.lt_or_ge 978128209754444873 n with h8 | h8
        · -- n > 978128209754444873
          rcases Nat.lt_or_ge 980897440351610909 n with h10 | h10
          · -- n > 980897440351610909
            rcases Nat.lt_or_ge 983674647998656781 n with h12 | h12
            · -- n > 983674647998656781
              exact RamareSaouter2003.prime_interval_nat_ladder_c07037 n (by omega) (by omega)
            · -- n <= 983674647998656781
              exact RamareSaouter2003.prime_interval_nat_ladder_c07036 n (by omega) (by omega)
          · -- n <= 980897440351610909
            exact RamareSaouter2003.prime_interval_nat_ladder_c07035 n (by omega) (by omega)
        · -- n <= 978128209754444873
          rcases Nat.lt_or_ge 972612977354178619 n with h10 | h10
          · -- n > 972612977354178619
            rcases Nat.lt_or_ge 975366670155476999 n with h12 | h12
            · -- n > 975366670155476999
              exact RamareSaouter2003.prime_interval_nat_ladder_c07034 n (by omega) (by omega)
            · -- n <= 975366670155476999
              exact RamareSaouter2003.prime_interval_nat_ladder_c07033 n (by omega) (by omega)
          · -- n <= 972612977354178619
            exact RamareSaouter2003.prime_interval_nat_ladder_c07032 n (by omega) (by omega)
      · -- n <= 969867175623724759
        rcases Nat.lt_or_ge 961675758172387253 n with h8 | h8
        · -- n > 961675758172387253
          rcases Nat.lt_or_ge 964398464224085533 n with h10 | h10
          · -- n > 964398464224085533
            rcases Nat.lt_or_ge 967128966595397941 n with h12 | h12
            · -- n > 967128966595397941
              exact RamareSaouter2003.prime_interval_nat_ladder_c07031 n (by omega) (by omega)
            · -- n <= 967128966595397941
              exact RamareSaouter2003.prime_interval_nat_ladder_c07030 n (by omega) (by omega)
          · -- n <= 964398464224085533
            exact RamareSaouter2003.prime_interval_nat_ladder_c07029 n (by omega) (by omega)
        · -- n <= 961675758172387253
          rcases Nat.lt_or_ge 956253310241527159 n with h10 | h10
          · -- n > 956253310241527159
            rcases Nat.lt_or_ge 958960749502315949 n with h12 | h12
            · -- n > 958960749502315949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07028 n (by omega) (by omega)
            · -- n <= 958960749502315949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07027 n (by omega) (by omega)
          · -- n <= 956253310241527159
            exact RamareSaouter2003.prime_interval_nat_ladder_c07026 n (by omega) (by omega)
  · -- n <= 953553629797611407
    rcases Nat.lt_or_ge 919142588346435403 n with h4 | h4
    · -- n > 919142588346435403
      rcases Nat.lt_or_ge 934867519326371651 n with h6 | h6
      · -- n > 934867519326371651
        rcases Nat.lt_or_ge 942830663232420643 n with h8 | h8
        · -- n > 942830663232420643
          rcases Nat.lt_or_ge 948176929310435017 n with h10 | h10
          · -- n > 948176929310435017
            rcases Nat.lt_or_ge 950861484815253043 n with h12 | h12
            · -- n > 950861484815253043
              exact RamareSaouter2003.prime_interval_nat_ladder_c07025 n (by omega) (by omega)
            · -- n <= 950861484815253043
              exact RamareSaouter2003.prime_interval_nat_ladder_c07024 n (by omega) (by omega)
          · -- n <= 948176929310435017
            rcases Nat.lt_or_ge 945500058282143579 n with h12 | h12
            · -- n > 945500058282143579
              exact RamareSaouter2003.prime_interval_nat_ladder_c07023 n (by omega) (by omega)
            · -- n <= 945500058282143579
              exact RamareSaouter2003.prime_interval_nat_ladder_c07022 n (by omega) (by omega)
        · -- n <= 942830663232420643
          rcases Nat.lt_or_ge 937514415367271993 n with h10 | h10
          · -- n > 937514415367271993
            rcases Nat.lt_or_ge 940168757031926137 n with h12 | h12
            · -- n > 940168757031926137
              exact RamareSaouter2003.prime_interval_nat_ladder_c07021 n (by omega) (by omega)
            · -- n <= 940168757031926137
              exact RamareSaouter2003.prime_interval_nat_ladder_c07020 n (by omega) (by omega)
          · -- n <= 937514415367271993
            exact RamareSaouter2003.prime_interval_nat_ladder_c07019 n (by omega) (by omega)
      · -- n <= 934867519326371651
        rcases Nat.lt_or_ge 926971757385493429 n with h8 | h8
        · -- n > 926971757385493429
          rcases Nat.lt_or_ge 929596287234431381 n with h10 | h10
          · -- n > 929596287234431381
            rcases Nat.lt_or_ge 932228173111615511 n with h12 | h12
            · -- n > 932228173111615511
              exact RamareSaouter2003.prime_interval_nat_ladder_c07018 n (by omega) (by omega)
            · -- n <= 932228173111615511
              exact RamareSaouter2003.prime_interval_nat_ladder_c07017 n (by omega) (by omega)
          · -- n <= 929596287234431381
            exact RamareSaouter2003.prime_interval_nat_ladder_c07016 n (by omega) (by omega)
        · -- n <= 926971757385493429
          rcases Nat.lt_or_ge 921744955304889049 n with h10 | h10
          · -- n > 921744955304889049
            rcases Nat.lt_or_ge 924354666037514423 n with h12 | h12
            · -- n > 924354666037514423
              exact RamareSaouter2003.prime_interval_nat_ladder_c07015 n (by omega) (by omega)
            · -- n <= 924354666037514423
              exact RamareSaouter2003.prime_interval_nat_ladder_c07014 n (by omega) (by omega)
          · -- n <= 921744955304889049
            exact RamareSaouter2003.prime_interval_nat_ladder_c07013 n (by omega) (by omega)
    · -- n <= 919142588346435403
      rcases Nat.lt_or_ge 903682030545619223 n with h6 | h6
      · -- n > 903682030545619223
        rcases Nat.lt_or_ge 911379565312494599 n with h8 | h8
        · -- n > 911379565312494599
          rcases Nat.lt_or_ge 913959898430263871 n with h10 | h10
          · -- n > 913959898430263871
            rcases Nat.lt_or_ge 916547578399028567 n with h12 | h12
            · -- n > 916547578399028567
              exact RamareSaouter2003.prime_interval_nat_ladder_c07012 n (by omega) (by omega)
            · -- n <= 916547578399028567
              exact RamareSaouter2003.prime_interval_nat_ladder_c07011 n (by omega) (by omega)
          · -- n <= 913959898430263871
            exact RamareSaouter2003.prime_interval_nat_ladder_c07010 n (by omega) (by omega)
        · -- n <= 911379565312494599
          rcases Nat.lt_or_ge 906240616214392007 n with h10 | h10
          · -- n > 906240616214392007
            rcases Nat.lt_or_ge 908806460438824391 n with h12 | h12
            · -- n > 908806460438824391
              exact RamareSaouter2003.prime_interval_nat_ladder_c07009 n (by omega) (by omega)
            · -- n <= 908806460438824391
              exact RamareSaouter2003.prime_interval_nat_ladder_c07008 n (by omega) (by omega)
          · -- n <= 906240616214392007
            exact RamareSaouter2003.prime_interval_nat_ladder_c07007 n (by omega) (by omega)
      · -- n <= 903682030545619223
        rcases Nat.lt_or_ge 896049529144866959 n with h8 | h8
        · -- n > 896049529144866959
          rcases Nat.lt_or_ge 898586499457952813 n with h10 | h10
          · -- n > 898586499457952813
            rcases Nat.lt_or_ge 901130659602714539 n with h12 | h12
            · -- n > 901130659602714539
              exact RamareSaouter2003.prime_interval_nat_ladder_c07006 n (by omega) (by omega)
            · -- n <= 901130659602714539
              exact RamareSaouter2003.prime_interval_nat_ladder_c07005 n (by omega) (by omega)
          · -- n <= 898586499457952813
            exact RamareSaouter2003.prime_interval_nat_ladder_c07004 n (by omega) (by omega)
        · -- n <= 896049529144866959
          rcases Nat.lt_or_ge 890997021386658443 n with h10 | h10
          · -- n > 890997021386658443
            rcases Nat.lt_or_ge 893519706882204343 n with h12 | h12
            · -- n > 893519706882204343
              exact RamareSaouter2003.prime_interval_nat_ladder_c07003 n (by omega) (by omega)
            · -- n <= 893519706882204343
              exact RamareSaouter2003.prime_interval_nat_ladder_c07002 n (by omega) (by omega)
          · -- n <= 890997021386658443
            exact RamareSaouter2003.prime_interval_nat_ladder_c07001 n (by omega) (by omega)
