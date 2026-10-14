-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp043
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T15:56:54.912645+00:00
-- url     : https://prove2.me/submissions/de53c009-5582-4c70-b8a7-957decc52aed

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02101
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02102
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02103
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02104
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02105
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02106
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02107
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02108
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02109
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02110
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02111
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02112
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02113
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02114
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02115
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02116
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02117
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02118
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02119
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02120
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02121
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02122
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02123
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02124
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02125
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02126
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02127
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02128
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02129
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02130
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02131
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02132
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02133
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02134
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02135
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02136
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02137
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02138
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02139
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02140
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02141
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02142
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02143
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02144
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02145
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02146
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02147
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02148
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02149
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02150

theorem solution (n : Nat)
    (hn : 1616505218459 < n) (hupper : n <= 1834768879973) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1722201640213 n with h2 | h2
  · -- n > 1722201640213
    rcases Nat.lt_or_ge 1775349746747 n with h4 | h4
    · -- n > 1775349746747
      rcases Nat.lt_or_ge 1802532326687 n with h6 | h6
      · -- n > 1802532326687
        rcases Nat.lt_or_ge 1816278434081 n with h8 | h8
        · -- n > 1816278434081
          rcases Nat.lt_or_ge 1825500374023 n with h10 | h10
          · -- n > 1825500374023
            rcases Nat.lt_or_ge 1830128791681 n with h12 | h12
            · -- n > 1830128791681
              exact RamareSaouter2003.prime_interval_nat_ladder_c02150 n (by omega) (by omega)
            · -- n <= 1830128791681
              exact RamareSaouter2003.prime_interval_nat_ladder_c02149 n (by omega) (by omega)
          · -- n <= 1825500374023
            rcases Nat.lt_or_ge 1820883597919 n with h12 | h12
            · -- n > 1820883597919
              exact RamareSaouter2003.prime_interval_nat_ladder_c02148 n (by omega) (by omega)
            · -- n <= 1820883597919
              exact RamareSaouter2003.prime_interval_nat_ladder_c02147 n (by omega) (by omega)
        · -- n <= 1816278434081
          rcases Nat.lt_or_ge 1807102827433 n with h10 | h10
          · -- n > 1807102827433
            rcases Nat.lt_or_ge 1811684853569 n with h12 | h12
            · -- n > 1811684853569
              exact RamareSaouter2003.prime_interval_nat_ladder_c02146 n (by omega) (by omega)
            · -- n <= 1811684853569
              exact RamareSaouter2003.prime_interval_nat_ladder_c02145 n (by omega) (by omega)
          · -- n <= 1807102827433
            exact RamareSaouter2003.prime_interval_nat_ladder_c02144 n (by omega) (by omega)
      · -- n <= 1802532326687
        rcases Nat.lt_or_ge 1788889689089 n with h8 | h8
        · -- n > 1788889689089
          rcases Nat.lt_or_ge 1793425786237 n with h10 | h10
          · -- n > 1793425786237
            rcases Nat.lt_or_ge 1797973322527 n with h12 | h12
            · -- n > 1797973322527
              exact RamareSaouter2003.prime_interval_nat_ladder_c02143 n (by omega) (by omega)
            · -- n <= 1797973322527
              exact RamareSaouter2003.prime_interval_nat_ladder_c02142 n (by omega) (by omega)
          · -- n <= 1793425786237
            exact RamareSaouter2003.prime_interval_nat_ladder_c02141 n (by omega) (by omega)
        · -- n <= 1788889689089
          rcases Nat.lt_or_ge 1779851697863 n with h10 | h10
          · -- n > 1779851697863
            rcases Nat.lt_or_ge 1784365002491 n with h12 | h12
            · -- n > 1784365002491
              exact RamareSaouter2003.prime_interval_nat_ladder_c02140 n (by omega) (by omega)
            · -- n <= 1784365002491
              exact RamareSaouter2003.prime_interval_nat_ladder_c02139 n (by omega) (by omega)
          · -- n <= 1779851697863
            exact RamareSaouter2003.prime_interval_nat_ladder_c02138 n (by omega) (by omega)
    · -- n <= 1775349746747
      rcases Nat.lt_or_ge 1748574878443 n with h6 | h6
      · -- n > 1748574878443
        rcases Nat.lt_or_ge 1761911730889 n with h8 | h8
        · -- n > 1761911730889
          rcases Nat.lt_or_ge 1766379791573 n with h10 | h10
          · -- n > 1766379791573
            rcases Nat.lt_or_ge 1770859120753 n with h12 | h12
            · -- n > 1770859120753
              exact RamareSaouter2003.prime_interval_nat_ladder_c02137 n (by omega) (by omega)
            · -- n <= 1770859120753
              exact RamareSaouter2003.prime_interval_nat_ladder_c02136 n (by omega) (by omega)
          · -- n <= 1766379791573
            exact RamareSaouter2003.prime_interval_nat_ladder_c02135 n (by omega) (by omega)
        · -- n <= 1761911730889
          rcases Nat.lt_or_ge 1753009302377 n with h10 | h10
          · -- n > 1753009302377
            rcases Nat.lt_or_ge 1757454910531 n with h12 | h12
            · -- n > 1757454910531
              exact RamareSaouter2003.prime_interval_nat_ladder_c02134 n (by omega) (by omega)
            · -- n <= 1757454910531
              exact RamareSaouter2003.prime_interval_nat_ladder_c02133 n (by omega) (by omega)
          · -- n <= 1753009302377
            exact RamareSaouter2003.prime_interval_nat_ladder_c02132 n (by omega) (by omega)
      · -- n <= 1748574878443
        rcases Nat.lt_or_ge 1735338432211 n with h8 | h8
        · -- n > 1735338432211
          rcases Nat.lt_or_ge 1739739471341 n with h10 | h10
          · -- n > 1739739471341
            rcases Nat.lt_or_ge 1744151610763 n with h12 | h12
            · -- n > 1744151610763
              exact RamareSaouter2003.prime_interval_nat_ladder_c02131 n (by omega) (by omega)
            · -- n <= 1744151610763
              exact RamareSaouter2003.prime_interval_nat_ladder_c02130 n (by omega) (by omega)
          · -- n <= 1739739471341
            exact RamareSaouter2003.prime_interval_nat_ladder_c02129 n (by omega) (by omega)
        · -- n <= 1735338432211
          rcases Nat.lt_or_ge 1726569544351 n with h10 | h10
          · -- n > 1726569544351
            rcases Nat.lt_or_ge 1730948465723 n with h12 | h12
            · -- n > 1730948465723
              exact RamareSaouter2003.prime_interval_nat_ladder_c02128 n (by omega) (by omega)
            · -- n <= 1730948465723
              exact RamareSaouter2003.prime_interval_nat_ladder_c02127 n (by omega) (by omega)
          · -- n <= 1726569544351
            exact RamareSaouter2003.prime_interval_nat_ladder_c02126 n (by omega) (by omega)
  · -- n <= 1722201640213
    rcases Nat.lt_or_ge 1666409011103 n with h4 | h4
    · -- n > 1666409011103
      rcases Nat.lt_or_ge 1691932488443 n with h6 | h6
      · -- n > 1691932488443
        rcases Nat.lt_or_ge 1704839646239 n with h8 | h8
        · -- n > 1704839646239
          rcases Nat.lt_or_ge 1713498773621 n with h10 | h10
          · -- n > 1713498773621
            rcases Nat.lt_or_ge 1717844725819 n with h12 | h12
            · -- n > 1717844725819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02125 n (by omega) (by omega)
            · -- n <= 1717844725819
              exact RamareSaouter2003.prime_interval_nat_ladder_c02124 n (by omega) (by omega)
          · -- n <= 1713498773621
            rcases Nat.lt_or_ge 1709163756191 n with h12 | h12
            · -- n > 1709163756191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02123 n (by omega) (by omega)
            · -- n <= 1709163756191
              exact RamareSaouter2003.prime_interval_nat_ladder_c02122 n (by omega) (by omega)
        · -- n <= 1704839646239
          rcases Nat.lt_or_ge 1696224039547 n with h10 | h10
          · -- n > 1696224039547
            rcases Nat.lt_or_ge 1700526416431 n with h12 | h12
            · -- n > 1700526416431
              exact RamareSaouter2003.prime_interval_nat_ladder_c02121 n (by omega) (by omega)
            · -- n <= 1700526416431
              exact RamareSaouter2003.prime_interval_nat_ladder_c02120 n (by omega) (by omega)
          · -- n <= 1696224039547
            exact RamareSaouter2003.prime_interval_nat_ladder_c02119 n (by omega) (by omega)
      · -- n <= 1691932488443
        rcases Nat.lt_or_ge 1679122519301 n with h8 | h8
        · -- n > 1679122519301
          rcases Nat.lt_or_ge 1683381755291 n with h10 | h10
          · -- n > 1683381755291
            rcases Nat.lt_or_ge 1687651736041 n with h12 | h12
            · -- n > 1687651736041
              exact RamareSaouter2003.prime_interval_nat_ladder_c02118 n (by omega) (by omega)
            · -- n <= 1687651736041
              exact RamareSaouter2003.prime_interval_nat_ladder_c02117 n (by omega) (by omega)
          · -- n <= 1683381755291
            exact RamareSaouter2003.prime_interval_nat_ladder_c02116 n (by omega) (by omega)
        · -- n <= 1679122519301
          rcases Nat.lt_or_ge 1670636173907 n with h10 | h10
          · -- n > 1670636173907
            rcases Nat.lt_or_ge 1674874001131 n with h12 | h12
            · -- n > 1674874001131
              exact RamareSaouter2003.prime_interval_nat_ladder_c02115 n (by omega) (by omega)
            · -- n <= 1674874001131
              exact RamareSaouter2003.prime_interval_nat_ladder_c02114 n (by omega) (by omega)
          · -- n <= 1670636173907
            exact RamareSaouter2003.prime_interval_nat_ladder_c02113 n (by omega) (by omega)
    · -- n <= 1666409011103
      rcases Nat.lt_or_ge 1641268492733 n with h6 | h6
      · -- n > 1641268492733
        rcases Nat.lt_or_ge 1653791241071 n with h8 | h8
        · -- n > 1653791241071
          rcases Nat.lt_or_ge 1657986571187 n with h10 | h10
          · -- n > 1657986571187
            rcases Nat.lt_or_ge 1662192485687 n with h12 | h12
            · -- n > 1662192485687
              exact RamareSaouter2003.prime_interval_nat_ladder_c02112 n (by omega) (by omega)
            · -- n <= 1662192485687
              exact RamareSaouter2003.prime_interval_nat_ladder_c02111 n (by omega) (by omega)
          · -- n <= 1657986571187
            exact RamareSaouter2003.prime_interval_nat_ladder_c02110 n (by omega) (by omega)
        · -- n <= 1653791241071
          rcases Nat.lt_or_ge 1645432228369 n with h10 | h10
          · -- n > 1645432228369
            rcases Nat.lt_or_ge 1649606468971 n with h12 | h12
            · -- n > 1649606468971
              exact RamareSaouter2003.prime_interval_nat_ladder_c02109 n (by omega) (by omega)
            · -- n <= 1649606468971
              exact RamareSaouter2003.prime_interval_nat_ladder_c02108 n (by omega) (by omega)
          · -- n <= 1645432228369
            exact RamareSaouter2003.prime_interval_nat_ladder_c02107 n (by omega) (by omega)
      · -- n <= 1641268492733
        rcases Nat.lt_or_ge 1628840053937 n with h8 | h8
        · -- n > 1628840053937
          rcases Nat.lt_or_ge 1632972431707 n with h10 | h10
          · -- n > 1632972431707
            rcases Nat.lt_or_ge 1637115235901 n with h12 | h12
            · -- n > 1637115235901
              exact RamareSaouter2003.prime_interval_nat_ladder_c02106 n (by omega) (by omega)
            · -- n <= 1637115235901
              exact RamareSaouter2003.prime_interval_nat_ladder_c02105 n (by omega) (by omega)
          · -- n <= 1632972431707
            exact RamareSaouter2003.prime_interval_nat_ladder_c02104 n (by omega) (by omega)
        · -- n <= 1628840053937
          rcases Nat.lt_or_ge 1620606473287 n with h10 | h10
          · -- n > 1620606473287
            rcases Nat.lt_or_ge 1624718076467 n with h12 | h12
            · -- n > 1624718076467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02103 n (by omega) (by omega)
            · -- n <= 1624718076467
              exact RamareSaouter2003.prime_interval_nat_ladder_c02102 n (by omega) (by omega)
          · -- n <= 1620606473287
            exact RamareSaouter2003.prime_interval_nat_ladder_c02101 n (by omega) (by omega)
