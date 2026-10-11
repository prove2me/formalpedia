-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp004
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-10T15:33:32.399446+00:00
-- url     : https://prove2.me/submissions/d602dbae-70dc-47dc-bbc4-7bf7d48df549

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c00200

theorem solution (n : Nat)
    (hn : 14843139557 < n) (hupper : n <= 16558044781) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 15676102961 n with h2 | h2
  · -- n > 15676102961
    rcases Nat.lt_or_ge 16093141637 n with h4 | h4
    · -- n > 16093141637
      rcases Nat.lt_or_ge 16305993689 n with h6 | h6
      · -- n > 16305993689
        rcases Nat.lt_or_ge 16413521077 n with h8 | h8
        · -- n > 16413521077
          rcases Nat.lt_or_ge 16485617429 n with h10 | h10
          · -- n > 16485617429
            rcases Nat.lt_or_ge 16521789601 n with h12 | h12
            · -- n > 16521789601
              exact RamareSaouter2003.prime_interval_nat_ladder_c00200 n (by omega) (by omega)
            · -- n <= 16521789601
              exact RamareSaouter2003.prime_interval_nat_ladder_c00199 n (by omega) (by omega)
          · -- n <= 16485617429
            rcases Nat.lt_or_ge 16449527993 n with h12 | h12
            · -- n > 16449527993
              exact RamareSaouter2003.prime_interval_nat_ladder_c00198 n (by omega) (by omega)
            · -- n <= 16449527993
              exact RamareSaouter2003.prime_interval_nat_ladder_c00197 n (by omega) (by omega)
        · -- n <= 16413521077
          rcases Nat.lt_or_ge 16341754139 n with h10 | h10
          · -- n > 16341754139
            rcases Nat.lt_or_ge 16377596549 n with h12 | h12
            · -- n > 16377596549
              exact RamareSaouter2003.prime_interval_nat_ladder_c00196 n (by omega) (by omega)
            · -- n <= 16377596549
              exact RamareSaouter2003.prime_interval_nat_ladder_c00195 n (by omega) (by omega)
          · -- n <= 16341754139
            exact RamareSaouter2003.prime_interval_nat_ladder_c00194 n (by omega) (by omega)
      · -- n <= 16305993689
        rcases Nat.lt_or_ge 16199202223 n with h8 | h8
        · -- n > 16199202223
          rcases Nat.lt_or_ge 16234717921 n with h10 | h10
          · -- n > 16234717921
            rcases Nat.lt_or_ge 16270315013 n with h12 | h12
            · -- n > 16270315013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00193 n (by omega) (by omega)
            · -- n <= 16270315013
              exact RamareSaouter2003.prime_interval_nat_ladder_c00192 n (by omega) (by omega)
          · -- n <= 16234717921
            exact RamareSaouter2003.prime_interval_nat_ladder_c00191 n (by omega) (by omega)
        · -- n <= 16199202223
          rcases Nat.lt_or_ge 16128414287 n with h10 | h10
          · -- n > 16128414287
            rcases Nat.lt_or_ge 16163767777 n with h12 | h12
            · -- n > 16163767777
              exact RamareSaouter2003.prime_interval_nat_ladder_c00190 n (by omega) (by omega)
            · -- n <= 16163767777
              exact RamareSaouter2003.prime_interval_nat_ladder_c00189 n (by omega) (by omega)
          · -- n <= 16128414287
            exact RamareSaouter2003.prime_interval_nat_ladder_c00188 n (by omega) (by omega)
    · -- n <= 16093141637
      rcases Nat.lt_or_ge 15883191829 n with h6 | h6
      · -- n > 15883191829
        rcases Nat.lt_or_ge 15987806641 n with h8 | h8
        · -- n > 15987806641
          rcases Nat.lt_or_ge 16022838017 n with h10 | h10
          · -- n > 16022838017
            rcases Nat.lt_or_ge 16057949597 n with h12 | h12
            · -- n > 16057949597
              exact RamareSaouter2003.prime_interval_nat_ladder_c00187 n (by omega) (by omega)
            · -- n <= 16057949597
              exact RamareSaouter2003.prime_interval_nat_ladder_c00186 n (by omega) (by omega)
          · -- n <= 16022838017
            exact RamareSaouter2003.prime_interval_nat_ladder_c00185 n (by omega) (by omega)
        · -- n <= 15987806641
          rcases Nat.lt_or_ge 15917983717 n with h10 | h10
          · -- n > 15917983717
            rcases Nat.lt_or_ge 15952855241 n with h12 | h12
            · -- n > 15952855241
              exact RamareSaouter2003.prime_interval_nat_ladder_c00184 n (by omega) (by omega)
            · -- n <= 15952855241
              exact RamareSaouter2003.prime_interval_nat_ladder_c00183 n (by omega) (by omega)
          · -- n <= 15917983717
            exact RamareSaouter2003.prime_interval_nat_ladder_c00182 n (by omega) (by omega)
      · -- n <= 15883191829
        rcases Nat.lt_or_ge 15779292329 n with h8 | h8
        · -- n > 15779292329
          rcases Nat.lt_or_ge 15813846343 n with h10 | h10
          · -- n > 15813846343
            rcases Nat.lt_or_ge 15848479469 n with h12 | h12
            · -- n > 15848479469
              exact RamareSaouter2003.prime_interval_nat_ladder_c00181 n (by omega) (by omega)
            · -- n <= 15848479469
              exact RamareSaouter2003.prime_interval_nat_ladder_c00180 n (by omega) (by omega)
          · -- n <= 15813846343
            exact RamareSaouter2003.prime_interval_nat_ladder_c00179 n (by omega) (by omega)
        · -- n <= 15779292329
          rcases Nat.lt_or_ge 15710420861 n with h10 | h10
          · -- n > 15710420861
            rcases Nat.lt_or_ge 15744817169 n with h12 | h12
            · -- n > 15744817169
              exact RamareSaouter2003.prime_interval_nat_ladder_c00178 n (by omega) (by omega)
            · -- n <= 15744817169
              exact RamareSaouter2003.prime_interval_nat_ladder_c00177 n (by omega) (by omega)
          · -- n <= 15710420861
            exact RamareSaouter2003.prime_interval_nat_ladder_c00176 n (by omega) (by omega)
  · -- n <= 15676102961
    rcases Nat.lt_or_ge 15237032257 n with h4 | h4
    · -- n > 15237032257
      rcases Nat.lt_or_ge 15438061027 n with h6 | h6
      · -- n > 15438061027
        rcases Nat.lt_or_ge 15539612969 n with h8 | h8
        · -- n > 15539612969
          rcases Nat.lt_or_ge 15607702081 n with h10 | h10
          · -- n > 15607702081
            rcases Nat.lt_or_ge 15641863463 n with h12 | h12
            · -- n > 15641863463
              exact RamareSaouter2003.prime_interval_nat_ladder_c00175 n (by omega) (by omega)
            · -- n <= 15641863463
              exact RamareSaouter2003.prime_interval_nat_ladder_c00174 n (by omega) (by omega)
          · -- n <= 15607702081
            rcases Nat.lt_or_ge 15573618629 n with h12 | h12
            · -- n > 15573618629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00173 n (by omega) (by omega)
            · -- n <= 15573618629
              exact RamareSaouter2003.prime_interval_nat_ladder_c00172 n (by omega) (by omega)
        · -- n <= 15539612969
          rcases Nat.lt_or_ge 15471834269 n with h10 | h10
          · -- n > 15471834269
            rcases Nat.lt_or_ge 15505684913 n with h12 | h12
            · -- n > 15505684913
              exact RamareSaouter2003.prime_interval_nat_ladder_c00171 n (by omega) (by omega)
            · -- n <= 15505684913
              exact RamareSaouter2003.prime_interval_nat_ladder_c00170 n (by omega) (by omega)
          · -- n <= 15471834269
            exact RamareSaouter2003.prime_interval_nat_ladder_c00169 n (by omega) (by omega)
      · -- n <= 15438061027
        rcases Nat.lt_or_ge 15337202369 n with h8 | h8
        · -- n > 15337202369
          rcases Nat.lt_or_ge 15370745197 n with h10 | h10
          · -- n > 15370745197
            rcases Nat.lt_or_ge 15404364671 n with h12 | h12
            · -- n > 15404364671
              exact RamareSaouter2003.prime_interval_nat_ladder_c00168 n (by omega) (by omega)
            · -- n <= 15404364671
              exact RamareSaouter2003.prime_interval_nat_ladder_c00167 n (by omega) (by omega)
          · -- n <= 15370745197
            exact RamareSaouter2003.prime_interval_nat_ladder_c00166 n (by omega) (by omega)
        · -- n <= 15337202369
          rcases Nat.lt_or_ge 15270346127 n with h10 | h10
          · -- n > 15270346127
            rcases Nat.lt_or_ge 15303736087 n with h12 | h12
            · -- n > 15303736087
              exact RamareSaouter2003.prime_interval_nat_ladder_c00165 n (by omega) (by omega)
            · -- n <= 15303736087
              exact RamareSaouter2003.prime_interval_nat_ladder_c00164 n (by omega) (by omega)
          · -- n <= 15270346127
            exact RamareSaouter2003.prime_interval_nat_ladder_c00163 n (by omega) (by omega)
    · -- n <= 15237032257
      rcases Nat.lt_or_ge 15038738063 n with h6 | h6
      · -- n > 15038738063
        rcases Nat.lt_or_ge 15137545853 n with h8 | h8
        · -- n > 15137545853
          rcases Nat.lt_or_ge 15170632333 n with h10 | h10
          · -- n > 15170632333
            rcases Nat.lt_or_ge 15203794343 n with h12 | h12
            · -- n > 15203794343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00162 n (by omega) (by omega)
            · -- n <= 15203794343
              exact RamareSaouter2003.prime_interval_nat_ladder_c00161 n (by omega) (by omega)
          · -- n <= 15170632333
            exact RamareSaouter2003.prime_interval_nat_ladder_c00160 n (by omega) (by omega)
        · -- n <= 15137545853
          rcases Nat.lt_or_ge 15071598901 n with h10 | h10
          · -- n > 15071598901
            rcases Nat.lt_or_ge 15104534719 n with h12 | h12
            · -- n > 15104534719
              exact RamareSaouter2003.prime_interval_nat_ladder_c00159 n (by omega) (by omega)
            · -- n <= 15104534719
              exact RamareSaouter2003.prime_interval_nat_ladder_c00158 n (by omega) (by omega)
          · -- n <= 15071598901
            exact RamareSaouter2003.prime_interval_nat_ladder_c00157 n (by omega) (by omega)
      · -- n <= 15038738063
        rcases Nat.lt_or_ge 14940604223 n with h8 | h8
        · -- n > 14940604223
          rcases Nat.lt_or_ge 14973240929 n with h10 | h10
          · -- n > 14973240929
            rcases Nat.lt_or_ge 15005952109 n with h12 | h12
            · -- n > 15005952109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00156 n (by omega) (by omega)
            · -- n <= 15005952109
              exact RamareSaouter2003.prime_interval_nat_ladder_c00155 n (by omega) (by omega)
          · -- n <= 14973240929
            exact RamareSaouter2003.prime_interval_nat_ladder_c00154 n (by omega) (by omega)
        · -- n <= 14940604223
          rcases Nat.lt_or_ge 14875553747 n with h10 | h10
          · -- n > 14875553747
            rcases Nat.lt_or_ge 14908041901 n with h12 | h12
            · -- n > 14908041901
              exact RamareSaouter2003.prime_interval_nat_ladder_c00153 n (by omega) (by omega)
            · -- n <= 14908041901
              exact RamareSaouter2003.prime_interval_nat_ladder_c00152 n (by omega) (by omega)
          · -- n <= 14875553747
            exact RamareSaouter2003.prime_interval_nat_ladder_c00151 n (by omega) (by omega)
