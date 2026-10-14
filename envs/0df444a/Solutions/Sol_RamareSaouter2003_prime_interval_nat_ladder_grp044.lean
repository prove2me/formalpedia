-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp044
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-11T16:29:29.75001+00:00
-- url     : https://prove2.me/submissions/6bb79751-abd1-427e-9791-df7da3fd74f9

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c02200

theorem solution (n : Nat)
    (hn : 1834768879973 < n) (hupper : n <= 2082320379773) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1954650948611 n with h2 | h2
  · -- n > 1954650948611
    rcases Nat.lt_or_ge 2014930183571 n with h4 | h4
    · -- n > 2014930183571
      rcases Nat.lt_or_ge 2045759491103 n with h6 | h6
      · -- n > 2045759491103
        rcases Nat.lt_or_ge 2061349609199 n with h8 | h8
        · -- n > 2061349609199
          rcases Nat.lt_or_ge 2071808606743 n with h10 | h10
          · -- n > 2071808606743
            rcases Nat.lt_or_ge 2077057879711 n with h12 | h12
            · -- n > 2077057879711
              exact RamareSaouter2003.prime_interval_nat_ladder_c02200 n (by omega) (by omega)
            · -- n <= 2077057879711
              exact RamareSaouter2003.prime_interval_nat_ladder_c02199 n (by omega) (by omega)
          · -- n <= 2071808606743
            rcases Nat.lt_or_ge 2066572527529 n with h12 | h12
            · -- n > 2066572527529
              exact RamareSaouter2003.prime_interval_nat_ladder_c02198 n (by omega) (by omega)
            · -- n <= 2066572527529
              exact RamareSaouter2003.prime_interval_nat_ladder_c02197 n (by omega) (by omega)
        · -- n <= 2061349609199
          rcases Nat.lt_or_ge 2050943123627 n with h10 | h10
          · -- n > 2050943123627
            rcases Nat.lt_or_ge 2056139818841 n with h12 | h12
            · -- n > 2056139818841
              exact RamareSaouter2003.prime_interval_nat_ladder_c02196 n (by omega) (by omega)
            · -- n <= 2056139818841
              exact RamareSaouter2003.prime_interval_nat_ladder_c02195 n (by omega) (by omega)
          · -- n <= 2050943123627
            exact RamareSaouter2003.prime_interval_nat_ladder_c02194 n (by omega) (by omega)
      · -- n <= 2045759491103
        rcases Nat.lt_or_ge 2030286641701 n with h8 | h8
        · -- n > 2030286641701
          rcases Nat.lt_or_ge 2035431282581 n with h10 | h10
          · -- n > 2035431282581
            rcases Nat.lt_or_ge 2040588888137 n with h12 | h12
            · -- n > 2040588888137
              exact RamareSaouter2003.prime_interval_nat_ladder_c02193 n (by omega) (by omega)
            · -- n <= 2040588888137
              exact RamareSaouter2003.prime_interval_nat_ladder_c02192 n (by omega) (by omega)
          · -- n <= 2035431282581
            exact RamareSaouter2003.prime_interval_nat_ladder_c02191 n (by omega) (by omega)
        · -- n <= 2030286641701
          rcases Nat.lt_or_ge 2020036124441 n with h10 | h10
          · -- n > 2020036124441
            rcases Nat.lt_or_ge 2025154933051 n with h12 | h12
            · -- n > 2025154933051
              exact RamareSaouter2003.prime_interval_nat_ladder_c02190 n (by omega) (by omega)
            · -- n <= 2025154933051
              exact RamareSaouter2003.prime_interval_nat_ladder_c02189 n (by omega) (by omega)
          · -- n <= 2020036124441
            exact RamareSaouter2003.prime_interval_nat_ladder_c02188 n (by omega) (by omega)
    · -- n <= 2014930183571
      rcases Nat.lt_or_ge 1984562965531 n with h6 | h6
      · -- n > 1984562965531
        rcases Nat.lt_or_ge 1999689246391 n with h8 | h8
        · -- n > 1999689246391
          rcases Nat.lt_or_ge 2004756776677 n with h10 | h10
          · -- n > 2004756776677
            rcases Nat.lt_or_ge 2009837078419 n with h12 | h12
            · -- n > 2009837078419
              exact RamareSaouter2003.prime_interval_nat_ladder_c02187 n (by omega) (by omega)
            · -- n <= 2009837078419
              exact RamareSaouter2003.prime_interval_nat_ladder_c02186 n (by omega) (by omega)
          · -- n <= 2004756776677
            exact RamareSaouter2003.prime_interval_nat_ladder_c02185 n (by omega) (by omega)
        · -- n <= 1999689246391
          rcases Nat.lt_or_ge 1989592372619 n with h10 | h10
          · -- n > 1989592372619
            rcases Nat.lt_or_ge 1994634455651 n with h12 | h12
            · -- n > 1994634455651
              exact RamareSaouter2003.prime_interval_nat_ladder_c02184 n (by omega) (by omega)
            · -- n <= 1994634455651
              exact RamareSaouter2003.prime_interval_nat_ladder_c02183 n (by omega) (by omega)
          · -- n <= 1989592372619
            exact RamareSaouter2003.prime_interval_nat_ladder_c02182 n (by omega) (by omega)
      · -- n <= 1984562965531
        rcases Nat.lt_or_ge 1969550483479 n with h8 | h8
        · -- n > 1969550483479
          rcases Nat.lt_or_ge 1974542052583 n with h10 | h10
          · -- n > 1974542052583
            rcases Nat.lt_or_ge 1979546202791 n with h12 | h12
            · -- n > 1979546202791
              exact RamareSaouter2003.prime_interval_nat_ladder_c02181 n (by omega) (by omega)
            · -- n <= 1979546202791
              exact RamareSaouter2003.prime_interval_nat_ladder_c02180 n (by omega) (by omega)
          · -- n <= 1974542052583
            exact RamareSaouter2003.prime_interval_nat_ladder_c02179 n (by omega) (by omega)
        · -- n <= 1969550483479
          rcases Nat.lt_or_ge 1959604962797 n with h10 | h10
          · -- n > 1959604962797
            rcases Nat.lt_or_ge 1964571463993 n with h12 | h12
            · -- n > 1964571463993
              exact RamareSaouter2003.prime_interval_nat_ladder_c02178 n (by omega) (by omega)
            · -- n <= 1964571463993
              exact RamareSaouter2003.prime_interval_nat_ladder_c02177 n (by omega) (by omega)
          · -- n <= 1959604962797
            exact RamareSaouter2003.prime_interval_nat_ladder_c02176 n (by omega) (by omega)
  · -- n <= 1954650948611
    rcases Nat.lt_or_ge 1891370977291 n with h4 | h4
    · -- n > 1891370977291
      rcases Nat.lt_or_ge 1920319871077 n with h6 | h6
      · -- n > 1920319871077
        rcases Nat.lt_or_ge 1934959138009 n with h8 | h8
        · -- n > 1934959138009
          rcases Nat.lt_or_ge 1944780256213 n with h10 | h10
          · -- n > 1944780256213
            rcases Nat.lt_or_ge 1949709390121 n with h12 | h12
            · -- n > 1949709390121
              exact RamareSaouter2003.prime_interval_nat_ladder_c02175 n (by omega) (by omega)
            · -- n <= 1949709390121
              exact RamareSaouter2003.prime_interval_nat_ladder_c02174 n (by omega) (by omega)
          · -- n <= 1944780256213
            rcases Nat.lt_or_ge 1939863515833 n with h12 | h12
            · -- n > 1939863515833
              exact RamareSaouter2003.prime_interval_nat_ladder_c02173 n (by omega) (by omega)
            · -- n <= 1939863515833
              exact RamareSaouter2003.prime_interval_nat_ladder_c02172 n (by omega) (by omega)
        · -- n <= 1934959138009
          rcases Nat.lt_or_ge 1925187346457 n with h10 | h10
          · -- n > 1925187346457
            rcases Nat.lt_or_ge 1930067091881 n with h12 | h12
            · -- n > 1930067091881
              exact RamareSaouter2003.prime_interval_nat_ladder_c02171 n (by omega) (by omega)
            · -- n <= 1930067091881
              exact RamareSaouter2003.prime_interval_nat_ladder_c02170 n (by omega) (by omega)
          · -- n <= 1925187346457
            exact RamareSaouter2003.prime_interval_nat_ladder_c02169 n (by omega) (by omega)
      · -- n <= 1920319871077
        rcases Nat.lt_or_ge 1905790758847 n with h8 | h8
        · -- n > 1905790758847
          rcases Nat.lt_or_ge 1910621607871 n with h10 | h10
          · -- n > 1910621607871
            rcases Nat.lt_or_ge 1915464635143 n with h12 | h12
            · -- n > 1915464635143
              exact RamareSaouter2003.prime_interval_nat_ladder_c02168 n (by omega) (by omega)
            · -- n <= 1915464635143
              exact RamareSaouter2003.prime_interval_nat_ladder_c02167 n (by omega) (by omega)
          · -- n <= 1910621607871
            exact RamareSaouter2003.prime_interval_nat_ladder_c02166 n (by omega) (by omega)
        · -- n <= 1905790758847
          rcases Nat.lt_or_ge 1896165473791 n with h10 | h10
          · -- n > 1896165473791
            rcases Nat.lt_or_ge 1900972057573 n with h12 | h12
            · -- n > 1900972057573
              exact RamareSaouter2003.prime_interval_nat_ladder_c02165 n (by omega) (by omega)
            · -- n <= 1900972057573
              exact RamareSaouter2003.prime_interval_nat_ladder_c02164 n (by omega) (by omega)
          · -- n <= 1896165473791
            exact RamareSaouter2003.prime_interval_nat_ladder_c02163 n (by omega) (by omega)
    · -- n <= 1891370977291
      rcases Nat.lt_or_ge 1862856137497 n with h6 | h6
      · -- n > 1862856137497
        rcases Nat.lt_or_ge 1877059707377 n with h8 | h8
        · -- n > 1877059707377
          rcases Nat.lt_or_ge 1881818124047 n with h10 | h10
          · -- n > 1881818124047
            rcases Nat.lt_or_ge 1886588537341 n with h12 | h12
            · -- n > 1886588537341
              exact RamareSaouter2003.prime_interval_nat_ladder_c02162 n (by omega) (by omega)
            · -- n <= 1886588537341
              exact RamareSaouter2003.prime_interval_nat_ladder_c02161 n (by omega) (by omega)
          · -- n <= 1881818124047
            exact RamareSaouter2003.prime_interval_nat_ladder_c02160 n (by omega) (by omega)
        · -- n <= 1877059707377
          rcases Nat.lt_or_ge 1867578743999 n with h10 | h10
          · -- n > 1867578743999
            rcases Nat.lt_or_ge 1872313257329 n with h12 | h12
            · -- n > 1872313257329
              exact RamareSaouter2003.prime_interval_nat_ladder_c02159 n (by omega) (by omega)
            · -- n <= 1872313257329
              exact RamareSaouter2003.prime_interval_nat_ladder_c02158 n (by omega) (by omega)
          · -- n <= 1867578743999
            exact RamareSaouter2003.prime_interval_nat_ladder_c02157 n (by omega) (by omega)
      · -- n <= 1862856137497
        rcases Nat.lt_or_ge 1848759461959 n with h8 | h8
        · -- n > 1848759461959
          rcases Nat.lt_or_ge 1853446526167 n with h10 | h10
          · -- n > 1853446526167
            rcases Nat.lt_or_ge 1858145408083 n with h12 | h12
            · -- n > 1858145408083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02156 n (by omega) (by omega)
            · -- n <= 1858145408083
              exact RamareSaouter2003.prime_interval_nat_ladder_c02155 n (by omega) (by omega)
          · -- n <= 1853446526167
            exact RamareSaouter2003.prime_interval_nat_ladder_c02154 n (by omega) (by omega)
        · -- n <= 1848759461959
          rcases Nat.lt_or_ge 1839420668227 n with h10 | h10
          · -- n > 1839420668227
            rcases Nat.lt_or_ge 1844084185753 n with h12 | h12
            · -- n > 1844084185753
              exact RamareSaouter2003.prime_interval_nat_ladder_c02153 n (by omega) (by omega)
            · -- n <= 1844084185753
              exact RamareSaouter2003.prime_interval_nat_ladder_c02152 n (by omega) (by omega)
          · -- n <= 1839420668227
            exact RamareSaouter2003.prime_interval_nat_ladder_c02151 n (by omega) (by omega)
