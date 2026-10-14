-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp124
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T21:32:39.235295+00:00
-- url     : https://prove2.me/submissions/3e2ff7d8-a47f-4123-b5b0-38f3462f3b9a

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c06200

theorem solution (n : Nat)
    (hn : 80348244495624299 < n) (hupper : n <= 92548121498906519) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 86232632838266429 n with h2 | h2
  · -- n > 86232632838266429
    rcases Nat.lt_or_ge 89208390101533673 n with h4 | h4
    · -- n > 89208390101533673
      rcases Nat.lt_or_ge 90734563077808073 n with h6 | h6
      · -- n > 90734563077808073
        rcases Nat.lt_or_ge 91507406596059331 n with h8 | h8
        · -- n > 91507406596059331
          rcases Nat.lt_or_ge 92026285848227803 n with h10 | h10
          · -- n > 92026285848227803
            rcases Nat.lt_or_ge 92286834534737911 n with h12 | h12
            · -- n > 92286834534737911
              exact RamareSaouter2003.prime_interval_nat_ladder_c06200 n (by omega) (by omega)
            · -- n <= 92286834534737911
              exact RamareSaouter2003.prime_interval_nat_ladder_c06199 n (by omega) (by omega)
          · -- n <= 92026285848227803
            rcases Nat.lt_or_ge 91766471393967449 n with h12 | h12
            · -- n > 91766471393967449
              exact RamareSaouter2003.prime_interval_nat_ladder_c06198 n (by omega) (by omega)
            · -- n <= 91766471393967449
              exact RamareSaouter2003.prime_interval_nat_ladder_c06197 n (by omega) (by omega)
        · -- n <= 91507406596059331
          rcases Nat.lt_or_ge 90991442190434399 n with h10 | h10
          · -- n > 90991442190434399
            rcases Nat.lt_or_ge 91249053528527329 n with h12 | h12
            · -- n > 91249053528527329
              exact RamareSaouter2003.prime_interval_nat_ladder_c06196 n (by omega) (by omega)
            · -- n <= 91249053528527329
              exact RamareSaouter2003.prime_interval_nat_ladder_c06195 n (by omega) (by omega)
          · -- n <= 90991442190434399
            exact RamareSaouter2003.prime_interval_nat_ladder_c06194 n (by omega) (by omega)
      · -- n <= 90734563077808073
        rcases Nat.lt_or_ge 89968244819961007 n with h8 | h8
        · -- n > 89968244819961007
          rcases Nat.lt_or_ge 90222968315664407 n with h10 | h10
          · -- n > 90222968315664407
            rcases Nat.lt_or_ge 90478392368247853 n with h12 | h12
            · -- n > 90478392368247853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06193 n (by omega) (by omega)
            · -- n <= 90478392368247853
              exact RamareSaouter2003.prime_interval_nat_ladder_c06192 n (by omega) (by omega)
          · -- n <= 90222968315664407
            exact RamareSaouter2003.prime_interval_nat_ladder_c06191 n (by omega) (by omega)
        · -- n <= 89968244819961007
          rcases Nat.lt_or_ge 89460959626501777 n with h10 | h10
          · -- n > 89460959626501777
            rcases Nat.lt_or_ge 89714240836030493 n with h12 | h12
            · -- n > 89714240836030493
              exact RamareSaouter2003.prime_interval_nat_ladder_c06190 n (by omega) (by omega)
            · -- n <= 89714240836030493
              exact RamareSaouter2003.prime_interval_nat_ladder_c06189 n (by omega) (by omega)
          · -- n <= 89460959626501777
            exact RamareSaouter2003.prime_interval_nat_ladder_c06188 n (by omega) (by omega)
    · -- n <= 89208390101533673
      rcases Nat.lt_or_ge 87707895089169059 n with h6 | h6
      · -- n > 87707895089169059
        rcases Nat.lt_or_ge 88454967440037889 n with h8 | h8
        · -- n > 88454967440037889
          rcases Nat.lt_or_ge 88705405628227879 n with h10 | h10
          · -- n > 88705405628227879
            rcases Nat.lt_or_ge 88956528921566213 n with h12 | h12
            · -- n > 88956528921566213
              exact RamareSaouter2003.prime_interval_nat_ladder_c06187 n (by omega) (by omega)
            · -- n <= 88956528921566213
              exact RamareSaouter2003.prime_interval_nat_ladder_c06186 n (by omega) (by omega)
          · -- n <= 88705405628227879
            exact RamareSaouter2003.prime_interval_nat_ladder_c06185 n (by omega) (by omega)
        · -- n <= 88454967440037889
          rcases Nat.lt_or_ge 87956213068290239 n with h10 | h10
          · -- n > 87956213068290239
            rcases Nat.lt_or_ge 88205240842124093 n with h12 | h12
            · -- n > 88205240842124093
              exact RamareSaouter2003.prime_interval_nat_ladder_c06184 n (by omega) (by omega)
            · -- n <= 88205240842124093
              exact RamareSaouter2003.prime_interval_nat_ladder_c06183 n (by omega) (by omega)
          · -- n <= 87956213068290239
            exact RamareSaouter2003.prime_interval_nat_ladder_c06182 n (by omega) (by omega)
      · -- n <= 87707895089169059
        rcases Nat.lt_or_ge 86967131570530073 n with h8 | h8
        · -- n > 86967131570530073
          rcases Nat.lt_or_ge 87213354644356211 n with h10 | h10
          · -- n > 87213354644356211
            rcases Nat.lt_or_ge 87460273536920881 n with h12 | h12
            · -- n > 87460273536920881
              exact RamareSaouter2003.prime_interval_nat_ladder_c06181 n (by omega) (by omega)
            · -- n <= 87460273536920881
              exact RamareSaouter2003.prime_interval_nat_ladder_c06180 n (by omega) (by omega)
          · -- n <= 87213354644356211
            exact RamareSaouter2003.prime_interval_nat_ladder_c06179 n (by omega) (by omega)
        · -- n <= 86967131570530073
          rcases Nat.lt_or_ge 86476777163799247 n with h10 | h10
          · -- n > 86476777163799247
            rcases Nat.lt_or_ge 86721615303181933 n with h12 | h12
            · -- n > 86721615303181933
              exact RamareSaouter2003.prime_interval_nat_ladder_c06178 n (by omega) (by omega)
            · -- n <= 86721615303181933
              exact RamareSaouter2003.prime_interval_nat_ladder_c06177 n (by omega) (by omega)
          · -- n <= 86476777163799247
            exact RamareSaouter2003.prime_interval_nat_ladder_c06176 n (by omega) (by omega)
  · -- n <= 86232632838266429
    rcases Nat.lt_or_ge 83120932281033293 n with h4 | h4
    · -- n > 83120932281033293
      rcases Nat.lt_or_ge 84542928627709261 n with h6 | h6
      · -- n > 84542928627709261
        rcases Nat.lt_or_ge 85262990274017957 n with h8 | h8
        · -- n > 85262990274017957
          rcases Nat.lt_or_ge 85746440738063173 n with h10 | h10
          · -- n > 85746440738063173
            rcases Nat.lt_or_ge 85989194306851333 n with h12 | h12
            · -- n > 85989194306851333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06175 n (by omega) (by omega)
            · -- n <= 85989194306851333
              exact RamareSaouter2003.prime_interval_nat_ladder_c06174 n (by omega) (by omega)
          · -- n <= 85746440738063173
            rcases Nat.lt_or_ge 85504367758693151 n with h12 | h12
            · -- n > 85504367758693151
              exact RamareSaouter2003.prime_interval_nat_ladder_c06173 n (by omega) (by omega)
            · -- n <= 85504367758693151
              exact RamareSaouter2003.prime_interval_nat_ladder_c06172 n (by omega) (by omega)
        · -- n <= 85262990274017957
          rcases Nat.lt_or_ge 84782277382808149 n with h10 | h10
          · -- n > 84782277382808149
            rcases Nat.lt_or_ge 85022287514735047 n with h12 | h12
            · -- n > 85022287514735047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06171 n (by omega) (by omega)
            · -- n <= 85022287514735047
              exact RamareSaouter2003.prime_interval_nat_ladder_c06170 n (by omega) (by omega)
          · -- n <= 84782277382808149
            exact RamareSaouter2003.prime_interval_nat_ladder_c06169 n (by omega) (by omega)
      · -- n <= 84542928627709261
        rcases Nat.lt_or_ge 83828899633389109 n with h8 | h8
        · -- n > 83828899633389109
          rcases Nat.lt_or_ge 84066239411216477 n with h10 | h10
          · -- n > 84066239411216477
            rcases Nat.lt_or_ge 84304243381749473 n with h12 | h12
            · -- n > 84304243381749473
              exact RamareSaouter2003.prime_interval_nat_ladder_c06168 n (by omega) (by omega)
            · -- n <= 84304243381749473
              exact RamareSaouter2003.prime_interval_nat_ladder_c06167 n (by omega) (by omega)
          · -- n <= 84066239411216477
            exact RamareSaouter2003.prime_interval_nat_ladder_c06166 n (by omega) (by omega)
        · -- n <= 83828899633389109
          rcases Nat.lt_or_ge 83356241174155909 n with h10 | h10
          · -- n > 83356241174155909
            rcases Nat.lt_or_ge 83592244064872729 n with h12 | h12
            · -- n > 83592244064872729
              exact RamareSaouter2003.prime_interval_nat_ladder_c06165 n (by omega) (by omega)
            · -- n <= 83592244064872729
              exact RamareSaouter2003.prime_interval_nat_ladder_c06164 n (by omega) (by omega)
          · -- n <= 83356241174155909
            exact RamareSaouter2003.prime_interval_nat_ladder_c06163 n (by omega) (by omega)
    · -- n <= 83120932281033293
      rcases Nat.lt_or_ge 81722839144963193 n with h6 | h6
      · -- n > 81722839144963193
        rcases Nat.lt_or_ge 82418937312449971 n with h8 | h8
        · -- n > 82418937312449971
          rcases Nat.lt_or_ge 82652284029572941 n with h10 | h10
          · -- n > 82652284029572941
            rcases Nat.lt_or_ge 82886272108176857 n with h12 | h12
            · -- n > 82886272108176857
              exact RamareSaouter2003.prime_interval_nat_ladder_c06162 n (by omega) (by omega)
            · -- n <= 82886272108176857
              exact RamareSaouter2003.prime_interval_nat_ladder_c06161 n (by omega) (by omega)
          · -- n <= 82652284029572941
            exact RamareSaouter2003.prime_interval_nat_ladder_c06160 n (by omega) (by omega)
        · -- n <= 82418937312449971
          rcases Nat.lt_or_ge 81954219404304769 n with h10 | h10
          · -- n > 81954219404304769
            rcases Nat.lt_or_ge 82186253026395179 n with h12 | h12
            · -- n > 82186253026395179
              exact RamareSaouter2003.prime_interval_nat_ladder_c06159 n (by omega) (by omega)
            · -- n <= 82186253026395179
              exact RamareSaouter2003.prime_interval_nat_ladder_c06158 n (by omega) (by omega)
          · -- n <= 81954219404304769
            exact RamareSaouter2003.prime_interval_nat_ladder_c06157 n (by omega) (by omega)
      · -- n <= 81722839144963193
        rcases Nat.lt_or_ge 81032631270576257 n with h8 | h8
        · -- n > 81032631270576257
          rcases Nat.lt_or_ge 81262049598608237 n with h10 | h10
          · -- n > 81262049598608237
            rcases Nat.lt_or_ge 81492112524752399 n with h12 | h12
            · -- n > 81492112524752399
              exact RamareSaouter2003.prime_interval_nat_ladder_c06156 n (by omega) (by omega)
            · -- n <= 81492112524752399
              exact RamareSaouter2003.prime_interval_nat_ladder_c06155 n (by omega) (by omega)
          · -- n <= 81262049598608237
            exact RamareSaouter2003.prime_interval_nat_ladder_c06154 n (by omega) (by omega)
        · -- n <= 81032631270576257
          rcases Nat.lt_or_ge 80575725254249803 n with h10 | h10
          · -- n > 80575725254249803
            rcases Nat.lt_or_ge 80803856752904057 n with h12 | h12
            · -- n > 80803856752904057
              exact RamareSaouter2003.prime_interval_nat_ladder_c06153 n (by omega) (by omega)
            · -- n <= 80803856752904057
              exact RamareSaouter2003.prime_interval_nat_ladder_c06152 n (by omega) (by omega)
          · -- n <= 80575725254249803
            exact RamareSaouter2003.prime_interval_nat_ladder_c06151 n (by omega) (by omega)
