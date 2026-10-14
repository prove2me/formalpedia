-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp145
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T05:16:21.638549+00:00
-- url     : https://prove2.me/submissions/f4707938-bd34-4338-9b99-44e83a9a98e8

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07200
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07201
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07202
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07203
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07204
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07205
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07206
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07207
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07208
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07209
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07210
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07211
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07212
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07213
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07214
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07215
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07216
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07217
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07218
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07219
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07220
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07221
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07222
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07223
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07224
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07225
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07226
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07227
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07228
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07229
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07230
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07231
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07232
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07233
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07234
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07235
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07236
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07237
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07238
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07239
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07240
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07241
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07242
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07243
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07244
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07245
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07246
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07247

theorem solution (n : Nat)
    (hn : 1555129419536567443 < n) (hupper : n <= 1786208619689263597) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1664314896147708947 n with h2 | h2
  · -- n > 1664314896147708947
    rcases Nat.lt_or_ge 1721749572615998407 n with h4 | h4
    · -- n > 1721749572615998407
      rcases Nat.lt_or_ge 1751205534335583467 n with h6 | h6
      · -- n > 1751205534335583467
        rcases Nat.lt_or_ge 1766122092409985291 n with h8 | h8
        · -- n > 1766122092409985291
          rcases Nat.lt_or_ge 1776137011787332001 n with h10 | h10
          · -- n > 1776137011787332001
            rcases Nat.lt_or_ge 1781165596792354427 n with h12 | h12
            · -- n > 1781165596792354427
              exact RamareSaouter2003.prime_interval_nat_ladder_c07247 n (by omega) (by omega)
            · -- n <= 1781165596792354427
              exact RamareSaouter2003.prime_interval_nat_ladder_c07246 n (by omega) (by omega)
          · -- n <= 1776137011787332001
            rcases Nat.lt_or_ge 1771122521923675223 n with h12 | h12
            · -- n > 1771122521923675223
              exact RamareSaouter2003.prime_interval_nat_ladder_c07245 n (by omega) (by omega)
            · -- n <= 1771122521923675223
              exact RamareSaouter2003.prime_interval_nat_ladder_c07244 n (by omega) (by omega)
        · -- n <= 1766122092409985291
          rcases Nat.lt_or_ge 1756163661656159363 n with h10 | h10
          · -- n > 1756163661656159363
            rcases Nat.lt_or_ge 1761135900669375493 n with h12 | h12
            · -- n > 1761135900669375493
              exact RamareSaouter2003.prime_interval_nat_ladder_c07243 n (by omega) (by omega)
            · -- n <= 1761135900669375493
              exact RamareSaouter2003.prime_interval_nat_ladder_c07242 n (by omega) (by omega)
          · -- n <= 1756163661656159363
            exact RamareSaouter2003.prime_interval_nat_ladder_c07241 n (by omega) (by omega)
      · -- n <= 1751205534335583467
        rcases Nat.lt_or_ge 1736415064240270793 n with h8 | h8
        · -- n > 1736415064240270793
          rcases Nat.lt_or_ge 1741331176924832989 n with h10 | h10
          · -- n > 1741331176924832989
            rcases Nat.lt_or_ge 1746261345437563133 n with h12 | h12
            · -- n > 1746261345437563133
              exact RamareSaouter2003.prime_interval_nat_ladder_c07240 n (by omega) (by omega)
            · -- n <= 1746261345437563133
              exact RamareSaouter2003.prime_interval_nat_ladder_c07239 n (by omega) (by omega)
          · -- n <= 1741331176924832989
            exact RamareSaouter2003.prime_interval_nat_ladder_c07238 n (by omega) (by omega)
        · -- n <= 1736415064240270793
          rcases Nat.lt_or_ge 1726624280942528939 n with h10 | h10
          · -- n > 1726624280942528939
            rcases Nat.lt_or_ge 1731512883620641621 n with h12 | h12
            · -- n > 1731512883620641621
              exact RamareSaouter2003.prime_interval_nat_ladder_c07237 n (by omega) (by omega)
            · -- n <= 1731512883620641621
              exact RamareSaouter2003.prime_interval_nat_ladder_c07236 n (by omega) (by omega)
          · -- n <= 1726624280942528939
            exact RamareSaouter2003.prime_interval_nat_ladder_c07235 n (by omega) (by omega)
    · -- n <= 1721749572615998407
      rcases Nat.lt_or_ge 1692788598955354093 n with h6 | h6
      · -- n > 1692788598955354093
        rcases Nat.lt_or_ge 1707207692349521819 n with h8 | h8
        · -- n > 1707207692349521819
          rcases Nat.lt_or_ge 1712041295413776937 n with h10 | h10
          · -- n > 1712041295413776937
            rcases Nat.lt_or_ge 1716888597559616959 n with h12 | h12
            · -- n > 1716888597559616959
              exact RamareSaouter2003.prime_interval_nat_ladder_c07234 n (by omega) (by omega)
            · -- n <= 1716888597559616959
              exact RamareSaouter2003.prime_interval_nat_ladder_c07233 n (by omega) (by omega)
          · -- n <= 1712041295413776937
            exact RamareSaouter2003.prime_interval_nat_ladder_c07232 n (by omega) (by omega)
        · -- n <= 1707207692349521819
          rcases Nat.lt_or_ge 1697581388617244891 n with h10 | h10
          · -- n > 1697581388617244891
            rcases Nat.lt_or_ge 1702387709524403357 n with h12 | h12
            · -- n > 1702387709524403357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07231 n (by omega) (by omega)
            · -- n <= 1702387709524403357
              exact RamareSaouter2003.prime_interval_nat_ladder_c07230 n (by omega) (by omega)
          · -- n <= 1697581388617244891
            exact RamareSaouter2003.prime_interval_nat_ladder_c07229 n (by omega) (by omega)
      · -- n <= 1692788598955354093
        rcases Nat.lt_or_ge 1678491350248809071 n with h8 | h8
        · -- n > 1678491350248809071
          rcases Nat.lt_or_ge 1683243600722413291 n with h10 | h10
          · -- n > 1683243600722413291
            rcases Nat.lt_or_ge 1688009374576052243 n with h12 | h12
            · -- n > 1688009374576052243
              exact RamareSaouter2003.prime_interval_nat_ladder_c07228 n (by omega) (by omega)
            · -- n <= 1688009374576052243
              exact RamareSaouter2003.prime_interval_nat_ladder_c07227 n (by omega) (by omega)
          · -- n <= 1683243600722413291
            exact RamareSaouter2003.prime_interval_nat_ladder_c07226 n (by omega) (by omega)
        · -- n <= 1678491350248809071
          rcases Nat.lt_or_ge 1669027074104534233 n with h10 | h10
          · -- n > 1669027074104534233
            rcases Nat.lt_or_ge 1673752558073636533 n with h12 | h12
            · -- n > 1673752558073636533
              exact RamareSaouter2003.prime_interval_nat_ladder_c07225 n (by omega) (by omega)
            · -- n <= 1673752558073636533
              exact RamareSaouter2003.prime_interval_nat_ladder_c07224 n (by omega) (by omega)
          · -- n <= 1669027074104534233
            exact RamareSaouter2003.prime_interval_nat_ladder_c07223 n (by omega) (by omega)
  · -- n <= 1664314896147708947
    rcases Nat.lt_or_ge 1608796127411746643 n with h4 | h4
    · -- n > 1608796127411746643
      rcases Nat.lt_or_ge 1636320094067588393 n with h6 | h6
      · -- n > 1636320094067588393
        rcases Nat.lt_or_ge 1650258061042319549 n with h8 | h8
        · -- n > 1650258061042319549
          rcases Nat.lt_or_ge 1654930438331023837 n with h10 | h10
          · -- n > 1654930438331023837
            rcases Nat.lt_or_ge 1659616047557005327 n with h12 | h12
            · -- n > 1659616047557005327
              exact RamareSaouter2003.prime_interval_nat_ladder_c07222 n (by omega) (by omega)
            · -- n <= 1659616047557005327
              exact RamareSaouter2003.prime_interval_nat_ladder_c07221 n (by omega) (by omega)
          · -- n <= 1654930438331023837
            exact RamareSaouter2003.prime_interval_nat_ladder_c07220 n (by omega) (by omega)
        · -- n <= 1650258061042319549
          rcases Nat.lt_or_ge 1640952933391150133 n with h10 | h10
          · -- n > 1640952933391150133
            rcases Nat.lt_or_ge 1645598905535132599 n with h12 | h12
            · -- n > 1645598905535132599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07219 n (by omega) (by omega)
            · -- n <= 1645598905535132599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07218 n (by omega) (by omega)
          · -- n <= 1640952933391150133
            exact RamareSaouter2003.prime_interval_nat_ladder_c07217 n (by omega) (by omega)
      · -- n <= 1636320094067588393
        rcases Nat.lt_or_ge 1622499773540248469 n with h8 | h8
        · -- n > 1622499773540248469
          rcases Nat.lt_or_ge 1627093535238165971 n with h10 | h10
          · -- n > 1627093535238165971
            rcases Nat.lt_or_ge 1631700328593609961 n with h12 | h12
            · -- n > 1631700328593609961
              exact RamareSaouter2003.prime_interval_nat_ladder_c07216 n (by omega) (by omega)
            · -- n <= 1631700328593609961
              exact RamareSaouter2003.prime_interval_nat_ladder_c07215 n (by omega) (by omega)
          · -- n <= 1627093535238165971
            exact RamareSaouter2003.prime_interval_nat_ladder_c07214 n (by omega) (by omega)
        · -- n <= 1622499773540248469
          rcases Nat.lt_or_ge 1613351086704584819 n with h10 | h10
          · -- n > 1613351086704584819
            rcases Nat.lt_or_ge 1617918952232553101 n with h12 | h12
            · -- n > 1617918952232553101
              exact RamareSaouter2003.prime_interval_nat_ladder_c07213 n (by omega) (by omega)
            · -- n <= 1617918952232553101
              exact RamareSaouter2003.prime_interval_nat_ladder_c07212 n (by omega) (by omega)
          · -- n <= 1613351086704584819
            exact RamareSaouter2003.prime_interval_nat_ladder_c07211 n (by omega) (by omega)
    · -- n <= 1608796127411746643
      rcases Nat.lt_or_ge 1581735203262107591 n with h6 | h6
      · -- n > 1581735203262107591
        rcases Nat.lt_or_ge 1595208309213021299 n with h8 | h8
        · -- n > 1595208309213021299
          rcases Nat.lt_or_ge 1599724816338037867 n with h10 | h10
          · -- n > 1599724816338037867
            rcases Nat.lt_or_ge 1604254046385183899 n with h12 | h12
            · -- n > 1604254046385183899
              exact RamareSaouter2003.prime_interval_nat_ladder_c07210 n (by omega) (by omega)
            · -- n <= 1604254046385183899
              exact RamareSaouter2003.prime_interval_nat_ladder_c07209 n (by omega) (by omega)
          · -- n <= 1599724816338037867
            exact RamareSaouter2003.prime_interval_nat_ladder_c07208 n (by omega) (by omega)
        · -- n <= 1595208309213021299
          rcases Nat.lt_or_ge 1586213554842589961 n with h10 | h10
          · -- n > 1586213554842589961
            rcases Nat.lt_or_ge 1590704545928669903 n with h12 | h12
            · -- n > 1590704545928669903
              exact RamareSaouter2003.prime_interval_nat_ladder_c07207 n (by omega) (by omega)
            · -- n <= 1590704545928669903
              exact RamareSaouter2003.prime_interval_nat_ladder_c07206 n (by omega) (by omega)
          · -- n <= 1586213554842589961
            exact RamareSaouter2003.prime_interval_nat_ladder_c07205 n (by omega) (by omega)
      · -- n <= 1581735203262107591
        rcases Nat.lt_or_ge 1568375869004409203 n with h8 | h8
        · -- n > 1568375869004409203
          rcases Nat.lt_or_ge 1572816407140790269 n with h10 | h10
          · -- n > 1572816407140790269
            rcases Nat.lt_or_ge 1577269472085932761 n with h12 | h12
            · -- n > 1577269472085932761
              exact RamareSaouter2003.prime_interval_nat_ladder_c07204 n (by omega) (by omega)
            · -- n <= 1577269472085932761
              exact RamareSaouter2003.prime_interval_nat_ladder_c07203 n (by omega) (by omega)
          · -- n <= 1572816407140790269
            exact RamareSaouter2003.prime_interval_nat_ladder_c07202 n (by omega) (by omega)
        · -- n <= 1568375869004409203
          rcases Nat.lt_or_ge 1559532411725695061 n with h10 | h10
          · -- n > 1559532411725695061
            rcases Nat.lt_or_ge 1563947921001005599 n with h12 | h12
            · -- n > 1563947921001005599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07201 n (by omega) (by omega)
            · -- n <= 1563947921001005599
              exact RamareSaouter2003.prime_interval_nat_ladder_c07200 n (by omega) (by omega)
          · -- n <= 1559532411725695061
            exact RamareSaouter2003.prime_interval_nat_ladder_c07199 n (by omega) (by omega)
