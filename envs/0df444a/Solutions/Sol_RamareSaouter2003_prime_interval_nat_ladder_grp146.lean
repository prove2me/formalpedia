-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp146
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T05:42:04.428323+00:00
-- url     : https://prove2.me/submissions/3780319f-a203-460a-b693-6a4c1913b223

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07248
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07249
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07250
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07251
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07252
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07253
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07254
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07255
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07256
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07257
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07258
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07259
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07260
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07261
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07262
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07263
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07264
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07265
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07266
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07267
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07268
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07269
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07270
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07271
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07272
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07273
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07274
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07275
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07276
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07277
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07278
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07279
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07280
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07281
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07282
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07283
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07284
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07285
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07286
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07287
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07288
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07289
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07290
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07291
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07292
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07293
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07294
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07295
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c07296

theorem solution (n : Nat)
    (hn : 1786208619689263597 < n) (hupper : n <= 2051624730942508333) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 1911618212361708853 n with h2 | h2
  · -- n > 1911618212361708853
    rcases Nat.lt_or_ge 1977586964878371317 n with h4 | h4
    · -- n > 1977586964878371317
      rcases Nat.lt_or_ge 2011420197177474401 n with h6 | h6
      · -- n > 2011420197177474401
        rcases Nat.lt_or_ge 2028553295351783173 n with h8 | h8
        · -- n > 2028553295351783173
          rcases Nat.lt_or_ge 2040056395991073403 n with h10 | h10
          · -- n > 2040056395991073403
            rcases Nat.lt_or_ge 2045832399848804629 n with h12 | h12
            · -- n > 2045832399848804629
              exact RamareSaouter2003.prime_interval_nat_ladder_c07296 n (by omega) (by omega)
            · -- n <= 2045832399848804629
              exact RamareSaouter2003.prime_interval_nat_ladder_c07295 n (by omega) (by omega)
          · -- n <= 2040056395991073403
            rcases Nat.lt_or_ge 2034296726896596713 n with h12 | h12
            · -- n > 2034296726896596713
              exact RamareSaouter2003.prime_interval_nat_ladder_c07294 n (by omega) (by omega)
            · -- n <= 2034296726896596713
              exact RamareSaouter2003.prime_interval_nat_ladder_c07293 n (by omega) (by omega)
        · -- n <= 2028553295351783173
          rcases Nat.lt_or_ge 2017115101910032063 n with h10 | h10
          · -- n > 2017115101910032063
            rcases Nat.lt_or_ge 2022826104287309249 n with h12 | h12
            · -- n > 2022826104287309249
              exact RamareSaouter2003.prime_interval_nat_ladder_c07292 n (by omega) (by omega)
            · -- n <= 2022826104287309249
              exact RamareSaouter2003.prime_interval_nat_ladder_c07291 n (by omega) (by omega)
          · -- n <= 2017115101910032063
            exact RamareSaouter2003.prime_interval_nat_ladder_c07290 n (by omega) (by omega)
      · -- n <= 2011420197177474401
        rcases Nat.lt_or_ge 1994431853345018881 n with h8 | h8
        · -- n > 1994431853345018881
          rcases Nat.lt_or_ge 2000078609828487187 n with h10 | h10
          · -- n > 2000078609828487187
            rcases Nat.lt_or_ge 2005741407197865131 n with h12 | h12
            · -- n > 2005741407197865131
              exact RamareSaouter2003.prime_interval_nat_ladder_c07289 n (by omega) (by omega)
            · -- n <= 2005741407197865131
              exact RamareSaouter2003.prime_interval_nat_ladder_c07288 n (by omega) (by omega)
          · -- n <= 2000078609828487187
            exact RamareSaouter2003.prime_interval_nat_ladder_c07287 n (by omega) (by omega)
        · -- n <= 1994431853345018881
          rcases Nat.lt_or_ge 1983186089813373101 n with h10 | h10
          · -- n > 1983186089813373101
            rcases Nat.lt_or_ge 1988800982198435129 n with h12 | h12
            · -- n > 1988800982198435129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07286 n (by omega) (by omega)
            · -- n <= 1988800982198435129
              exact RamareSaouter2003.prime_interval_nat_ladder_c07285 n (by omega) (by omega)
          · -- n <= 1983186089813373101
            exact RamareSaouter2003.prime_interval_nat_ladder_c07284 n (by omega) (by omega)
    · -- n <= 1977586964878371317
      rcases Nat.lt_or_ge 1944323096629711531 n with h6 | h6
      · -- n > 1944323096629711531
        rcases Nat.lt_or_ge 1960884655113586777 n with h8 | h8
        · -- n > 1960884655113586777
          rcases Nat.lt_or_ge 1966436349925108657 n with h10 | h10
          · -- n > 1966436349925108657
            rcases Nat.lt_or_ge 1972003804355473949 n with h12 | h12
            · -- n > 1972003804355473949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07283 n (by omega) (by omega)
            · -- n <= 1972003804355473949
              exact RamareSaouter2003.prime_interval_nat_ladder_c07282 n (by omega) (by omega)
          · -- n <= 1966436349925108657
            exact RamareSaouter2003.prime_interval_nat_ladder_c07281 n (by omega) (by omega)
        · -- n <= 1960884655113586777
          rcases Nat.lt_or_ge 1949828047354607971 n with h10 | h10
          · -- n > 1949828047354607971
            rcases Nat.lt_or_ge 1955348490588634919 n with h12 | h12
            · -- n > 1955348490588634919
              exact RamareSaouter2003.prime_interval_nat_ladder_c07280 n (by omega) (by omega)
            · -- n <= 1955348490588634919
              exact RamareSaouter2003.prime_interval_nat_ladder_c07279 n (by omega) (by omega)
          · -- n <= 1949828047354607971
            exact RamareSaouter2003.prime_interval_nat_ladder_c07278 n (by omega) (by omega)
      · -- n <= 1944323096629711531
        rcases Nat.lt_or_ge 1927901300733662113 n with h8 | h8
        · -- n > 1927901300733662113
          rcases Nat.lt_or_ge 1933359767244505007 n with h10 | h10
          · -- n > 1933359767244505007
            rcases Nat.lt_or_ge 1938833672372019253 n with h12 | h12
            · -- n > 1938833672372019253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07277 n (by omega) (by omega)
            · -- n <= 1938833672372019253
              exact RamareSaouter2003.prime_interval_nat_ladder_c07276 n (by omega) (by omega)
          · -- n <= 1933359767244505007
            exact RamareSaouter2003.prime_interval_nat_ladder_c07275 n (by omega) (by omega)
        · -- n <= 1927901300733662113
          rcases Nat.lt_or_ge 1917030561383694769 n with h10 | h10
          · -- n > 1917030561383694769
            rcases Nat.lt_or_ge 1922458240239513797 n with h12 | h12
            · -- n > 1922458240239513797
              exact RamareSaouter2003.prime_interval_nat_ladder_c07274 n (by omega) (by omega)
            · -- n <= 1922458240239513797
              exact RamareSaouter2003.prime_interval_nat_ladder_c07273 n (by omega) (by omega)
          · -- n <= 1917030561383694769
            exact RamareSaouter2003.prime_interval_nat_ladder_c07272 n (by omega) (by omega)
  · -- n <= 1911618212361708853
    rcases Nat.lt_or_ge 1847849758981717703 n with h4 | h4
    · -- n > 1847849758981717703
      rcases Nat.lt_or_ge 1879463592114310409 n with h6 | h6
      · -- n > 1879463592114310409
        rcases Nat.lt_or_ge 1895472694680004763 n with h8 | h8
        · -- n > 1895472694680004763
          rcases Nat.lt_or_ge 1900839315434250991 n with h10 | h10
          · -- n > 1900839315434250991
            rcases Nat.lt_or_ge 1906221121792854367 n with h12 | h12
            · -- n > 1906221121792854367
              exact RamareSaouter2003.prime_interval_nat_ladder_c07271 n (by omega) (by omega)
            · -- n <= 1906221121792854367
              exact RamareSaouter2003.prime_interval_nat_ladder_c07270 n (by omega) (by omega)
          · -- n <= 1900839315434250991
            exact RamareSaouter2003.prime_interval_nat_ladder_c07269 n (by omega) (by omega)
        · -- n <= 1895472694680004763
          rcases Nat.lt_or_ge 1884784931031218197 n with h10 | h10
          · -- n > 1884784931031218197
            rcases Nat.lt_or_ge 1890121241150796611 n with h12 | h12
            · -- n > 1890121241150796611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07268 n (by omega) (by omega)
            · -- n <= 1890121241150796611
              exact RamareSaouter2003.prime_interval_nat_ladder_c07267 n (by omega) (by omega)
          · -- n <= 1884784931031218197
            exact RamareSaouter2003.prime_interval_nat_ladder_c07266 n (by omega) (by omega)
      · -- n <= 1879463592114310409
        rcases Nat.lt_or_ge 1863589606618775879 n with h8 | h8
        · -- n > 1863589606618775879
          rcases Nat.lt_or_ge 1868865983578914643 n with h10 | h10
          · -- n > 1868865983578914643
            rcases Nat.lt_or_ge 1874157316143421369 n with h12 | h12
            · -- n > 1874157316143421369
              exact RamareSaouter2003.prime_interval_nat_ladder_c07265 n (by omega) (by omega)
            · -- n <= 1874157316143421369
              exact RamareSaouter2003.prime_interval_nat_ladder_c07264 n (by omega) (by omega)
          · -- n <= 1868865983578914643
            exact RamareSaouter2003.prime_interval_nat_ladder_c07263 n (by omega) (by omega)
        · -- n <= 1863589606618775879
          rcases Nat.lt_or_ge 1853081527135754243 n with h10 | h10
          · -- n > 1853081527135754243
            rcases Nat.lt_or_ge 1858328131715191589 n with h12 | h12
            · -- n > 1858328131715191589
              exact RamareSaouter2003.prime_interval_nat_ladder_c07262 n (by omega) (by omega)
            · -- n <= 1858328131715191589
              exact RamareSaouter2003.prime_interval_nat_ladder_c07261 n (by omega) (by omega)
          · -- n <= 1853081527135754243
            exact RamareSaouter2003.prime_interval_nat_ladder_c07260 n (by omega) (by omega)
    · -- n <= 1847849758981717703
      rcases Nat.lt_or_ge 1816767800532160181 n with h6 | h6
      · -- n > 1816767800532160181
        rcases Nat.lt_or_ge 1832242888545416177 n with h8 | h8
        · -- n > 1832242888545416177
          rcases Nat.lt_or_ge 1837430450506085713 n with h10 | h10
          · -- n > 1837430450506085713
            rcases Nat.lt_or_ge 1842632711119480409 n with h12 | h12
            · -- n > 1842632711119480409
              exact RamareSaouter2003.prime_interval_nat_ladder_c07259 n (by omega) (by omega)
            · -- n <= 1842632711119480409
              exact RamareSaouter2003.prime_interval_nat_ladder_c07258 n (by omega) (by omega)
          · -- n <= 1837430450506085713
            exact RamareSaouter2003.prime_interval_nat_ladder_c07257 n (by omega) (by omega)
        · -- n <= 1832242888545416177
          rcases Nat.lt_or_ge 1821911533679200129 n with h10 | h10
          · -- n > 1821911533679200129
            rcases Nat.lt_or_ge 1827069913015059191 n with h12 | h12
            · -- n > 1827069913015059191
              exact RamareSaouter2003.prime_interval_nat_ladder_c07256 n (by omega) (by omega)
            · -- n <= 1827069913015059191
              exact RamareSaouter2003.prime_interval_nat_ladder_c07255 n (by omega) (by omega)
          · -- n <= 1821911533679200129
            exact RamareSaouter2003.prime_interval_nat_ladder_c07254 n (by omega) (by omega)
      · -- n <= 1816767800532160181
        rcases Nat.lt_or_ge 1801423379447027213 n with h8 | h8
        · -- n > 1801423379447027213
          rcases Nat.lt_or_ge 1806523704264271523 n with h10 | h10
          · -- n > 1806523704264271523
            rcases Nat.lt_or_ge 1811638499255588693 n with h12 | h12
            · -- n > 1811638499255588693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07253 n (by omega) (by omega)
            · -- n <= 1811638499255588693
              exact RamareSaouter2003.prime_interval_nat_ladder_c07252 n (by omega) (by omega)
          · -- n <= 1806523704264271523
            exact RamareSaouter2003.prime_interval_nat_ladder_c07251 n (by omega) (by omega)
        · -- n <= 1801423379447027213
          rcases Nat.lt_or_ge 1791265918484127521 n with h10 | h10
          · -- n > 1791265918484127521
            rcases Nat.lt_or_ge 1796337453842924423 n with h12 | h12
            · -- n > 1796337453842924423
              exact RamareSaouter2003.prime_interval_nat_ladder_c07250 n (by omega) (by omega)
            · -- n <= 1796337453842924423
              exact RamareSaouter2003.prime_interval_nat_ladder_c07249 n (by omega) (by omega)
          · -- n <= 1791265918484127521
            exact RamareSaouter2003.prime_interval_nat_ladder_c07248 n (by omega) (by omega)
