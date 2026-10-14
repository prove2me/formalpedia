-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp104
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T15:02:12.432848+00:00
-- url     : https://prove2.me/submissions/bb4cee40-7c0e-4e27-aed2-7d29a26c3f9b

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c05200

theorem solution (n : Nat)
    (hn : 4755668462802073 < n) (hupper : n <= 5477696691841147) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 5103921580248791 n with h2 | h2
  · -- n > 5103921580248791
    rcases Nat.lt_or_ge 5280044022670409 n with h4 | h4
    · -- n > 5280044022670409
      rcases Nat.lt_or_ge 5370366619570951 n with h6 | h6
      · -- n > 5370366619570951
        rcases Nat.lt_or_ge 5416108379394943 n with h8 | h8
        · -- n > 5416108379394943
          rcases Nat.lt_or_ge 5446813327101863 n with h10 | h10
          · -- n > 5446813327101863
            rcases Nat.lt_or_ge 5462231531271199 n with h12 | h12
            · -- n > 5462231531271199
              exact RamareSaouter2003.prime_interval_nat_ladder_c05200 n (by omega) (by omega)
            · -- n <= 5462231531271199
              exact RamareSaouter2003.prime_interval_nat_ladder_c05199 n (by omega) (by omega)
          · -- n <= 5446813327101863
            rcases Nat.lt_or_ge 5431435924656739 n with h12 | h12
            · -- n > 5431435924656739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05198 n (by omega) (by omega)
            · -- n <= 5431435924656739
              exact RamareSaouter2003.prime_interval_nat_ladder_c05197 n (by omega) (by omega)
        · -- n <= 5416108379394943
          rcases Nat.lt_or_ge 5385571380818231 n with h10 | h10
          · -- n > 5385571380818231
            rcases Nat.lt_or_ge 5400817184812633 n with h12 | h12
            · -- n > 5400817184812633
              exact RamareSaouter2003.prime_interval_nat_ladder_c05196 n (by omega) (by omega)
            · -- n <= 5400817184812633
              exact RamareSaouter2003.prime_interval_nat_ladder_c05195 n (by omega) (by omega)
          · -- n <= 5385571380818231
            exact RamareSaouter2003.prime_interval_nat_ladder_c05194 n (by omega) (by omega)
      · -- n <= 5370366619570951
        rcases Nat.lt_or_ge 5325012078897359 n with h8 | h8
        · -- n > 5325012078897359
          rcases Nat.lt_or_ge 5340088384354657 n with h10 | h10
          · -- n > 5340088384354657
            rcases Nat.lt_or_ge 5355207220096729 n with h12 | h12
            · -- n > 5355207220096729
              exact RamareSaouter2003.prime_interval_nat_ladder_c05193 n (by omega) (by omega)
            · -- n <= 5355207220096729
              exact RamareSaouter2003.prime_interval_nat_ladder_c05192 n (by omega) (by omega)
          · -- n <= 5340088384354657
            exact RamareSaouter2003.prime_interval_nat_ladder_c05191 n (by omega) (by omega)
        · -- n <= 5325012078897359
          rcases Nat.lt_or_ge 5294993270850553 n with h10 | h10
          · -- n > 5294993270850553
            rcases Nat.lt_or_ge 5309980407674707 n with h12 | h12
            · -- n > 5309980407674707
              exact RamareSaouter2003.prime_interval_nat_ladder_c05190 n (by omega) (by omega)
            · -- n <= 5309980407674707
              exact RamareSaouter2003.prime_interval_nat_ladder_c05189 n (by omega) (by omega)
          · -- n <= 5294993270850553
            exact RamareSaouter2003.prime_interval_nat_ladder_c05188 n (by omega) (by omega)
    · -- n <= 5280044022670409
      rcases Nat.lt_or_ge 5191234127984573 n with h6 | h6
      · -- n > 5191234127984573
        rcases Nat.lt_or_ge 5235451581755741 n with h8 | h8
        · -- n > 5235451581755741
          rcases Nat.lt_or_ge 5250274135813349 n with h10 | h10
          · -- n > 5250274135813349
            rcases Nat.lt_or_ge 5265137816922623 n with h12 | h12
            · -- n > 5265137816922623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05187 n (by omega) (by omega)
            · -- n <= 5265137816922623
              exact RamareSaouter2003.prime_interval_nat_ladder_c05186 n (by omega) (by omega)
          · -- n <= 5250274135813349
            exact RamareSaouter2003.prime_interval_nat_ladder_c05185 n (by omega) (by omega)
        · -- n <= 5235451581755741
          rcases Nat.lt_or_ge 5205931953101557 n with h10 | h10
          · -- n > 5205931953101557
            rcases Nat.lt_or_ge 5220671362943767 n with h12 | h12
            · -- n > 5220671362943767
              exact RamareSaouter2003.prime_interval_nat_ladder_c05184 n (by omega) (by omega)
            · -- n <= 5220671362943767
              exact RamareSaouter2003.prime_interval_nat_ladder_c05183 n (by omega) (by omega)
          · -- n <= 5205931953101557
            exact RamareSaouter2003.prime_interval_nat_ladder_c05182 n (by omega) (by omega)
      · -- n <= 5191234127984573
        rcases Nat.lt_or_ge 5147393314723739 n with h8 | h8
        · -- n > 5147393314723739
          rcases Nat.lt_or_ge 5161966336238359 n with h10 | h10
          · -- n > 5161966336238359
            rcases Nat.lt_or_ge 5176580820577853 n with h12 | h12
            · -- n > 5176580820577853
              exact RamareSaouter2003.prime_interval_nat_ladder_c05181 n (by omega) (by omega)
            · -- n <= 5176580820577853
              exact RamareSaouter2003.prime_interval_nat_ladder_c05180 n (by omega) (by omega)
          · -- n <= 5161966336238359
            exact RamareSaouter2003.prime_interval_nat_ladder_c05179 n (by omega) (by omega)
        · -- n <= 5147393314723739
          rcases Nat.lt_or_ge 5118370446929023 n with h10 | h10
          · -- n > 5118370446929023
            rcases Nat.lt_or_ge 5132860951097213 n with h12 | h12
            · -- n > 5132860951097213
              exact RamareSaouter2003.prime_interval_nat_ladder_c05178 n (by omega) (by omega)
            · -- n <= 5132860951097213
              exact RamareSaouter2003.prime_interval_nat_ladder_c05177 n (by omega) (by omega)
          · -- n <= 5118370446929023
            exact RamareSaouter2003.prime_interval_nat_ladder_c05176 n (by omega) (by omega)
  · -- n <= 5103921580248791
    rcases Nat.lt_or_ge 4919762228742619 n with h4 | h4
    · -- n > 4919762228742619
      rcases Nat.lt_or_ge 5003918495645899 n with h6 | h6
      · -- n > 5003918495645899
        rcases Nat.lt_or_ge 5046536198381719 n with h8 | h8
        · -- n > 5046536198381719
          rcases Nat.lt_or_ge 5075145092207261 n with h10 | h10
          · -- n > 5075145092207261
            rcases Nat.lt_or_ge 5089512538824521 n with h12 | h12
            · -- n > 5089512538824521
              exact RamareSaouter2003.prime_interval_nat_ladder_c05175 n (by omega) (by omega)
            · -- n <= 5089512538824521
              exact RamareSaouter2003.prime_interval_nat_ladder_c05174 n (by omega) (by omega)
          · -- n <= 5075145092207261
            rcases Nat.lt_or_ge 5060820999729401 n with h12 | h12
            · -- n > 5060820999729401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05173 n (by omega) (by omega)
            · -- n <= 5060820999729401
              exact RamareSaouter2003.prime_interval_nat_ladder_c05172 n (by omega) (by omega)
        · -- n <= 5046536198381719
          rcases Nat.lt_or_ge 5018083112380333 n with h10 | h10
          · -- n > 5018083112380333
            rcases Nat.lt_or_ge 5032289599212517 n with h12 | h12
            · -- n > 5032289599212517
              exact RamareSaouter2003.prime_interval_nat_ladder_c05171 n (by omega) (by omega)
            · -- n <= 5032289599212517
              exact RamareSaouter2003.prime_interval_nat_ladder_c05170 n (by omega) (by omega)
          · -- n <= 5018083112380333
            exact RamareSaouter2003.prime_interval_nat_ladder_c05169 n (by omega) (by omega)
      · -- n <= 5003918495645899
        rcases Nat.lt_or_ge 4961662954955281 n with h8 | h8
        · -- n > 4961662954955281
          rcases Nat.lt_or_ge 4975704339160883 n with h10 | h10
          · -- n > 4975704339160883
            rcases Nat.lt_or_ge 4989790993641227 n with h12 | h12
            · -- n > 4989790993641227
              exact RamareSaouter2003.prime_interval_nat_ladder_c05168 n (by omega) (by omega)
            · -- n <= 4989790993641227
              exact RamareSaouter2003.prime_interval_nat_ladder_c05167 n (by omega) (by omega)
          · -- n <= 4975704339160883
            exact RamareSaouter2003.prime_interval_nat_ladder_c05166 n (by omega) (by omega)
        · -- n <= 4961662954955281
          rcases Nat.lt_or_ge 4933691276032711 n with h10 | h10
          · -- n > 4933691276032711
            rcases Nat.lt_or_ge 4947656188366477 n with h12 | h12
            · -- n > 4947656188366477
              exact RamareSaouter2003.prime_interval_nat_ladder_c05165 n (by omega) (by omega)
            · -- n <= 4947656188366477
              exact RamareSaouter2003.prime_interval_nat_ladder_c05164 n (by omega) (by omega)
          · -- n <= 4933691276032711
            exact RamareSaouter2003.prime_interval_nat_ladder_c05163 n (by omega) (by omega)
    · -- n <= 4919762228742619
      rcases Nat.lt_or_ge 4837015101814531 n with h6 | h6
      · -- n > 4837015101814531
        rcases Nat.lt_or_ge 4878214335968531 n with h8 | h8
        · -- n > 4878214335968531
          rcases Nat.lt_or_ge 4892024474139377 n with h10 | h10
          · -- n > 4892024474139377
            rcases Nat.lt_or_ge 4905872901518249 n with h12 | h12
            · -- n > 4905872901518249
              exact RamareSaouter2003.prime_interval_nat_ladder_c05162 n (by omega) (by omega)
            · -- n <= 4905872901518249
              exact RamareSaouter2003.prime_interval_nat_ladder_c05161 n (by omega) (by omega)
          · -- n <= 4892024474139377
            exact RamareSaouter2003.prime_interval_nat_ladder_c05160 n (by omega) (by omega)
        · -- n <= 4878214335968531
          rcases Nat.lt_or_ge 4850710151318963 n with h10 | h10
          · -- n > 4850710151318963
            rcases Nat.lt_or_ge 4864441850596561 n with h12 | h12
            · -- n > 4864441850596561
              exact RamareSaouter2003.prime_interval_nat_ladder_c05159 n (by omega) (by omega)
            · -- n <= 4864441850596561
              exact RamareSaouter2003.prime_interval_nat_ladder_c05158 n (by omega) (by omega)
          · -- n <= 4850710151318963
            exact RamareSaouter2003.prime_interval_nat_ladder_c05157 n (by omega) (by omega)
      · -- n <= 4837015101814531
        rcases Nat.lt_or_ge 4796170234199251 n with h8 | h8
        · -- n > 4796170234199251
          rcases Nat.lt_or_ge 4809747591493357 n with h10 | h10
          · -- n > 4809747591493357
            rcases Nat.lt_or_ge 4823364980069323 n with h12 | h12
            · -- n > 4823364980069323
              exact RamareSaouter2003.prime_interval_nat_ladder_c05156 n (by omega) (by omega)
            · -- n <= 4823364980069323
              exact RamareSaouter2003.prime_interval_nat_ladder_c05155 n (by omega) (by omega)
          · -- n <= 4809747591493357
            exact RamareSaouter2003.prime_interval_nat_ladder_c05154 n (by omega) (by omega)
        · -- n <= 4796170234199251
          rcases Nat.lt_or_ge 4769130816340897 n with h10 | h10
          · -- n > 4769130816340897
            rcases Nat.lt_or_ge 4782630458643043 n with h12 | h12
            · -- n > 4782630458643043
              exact RamareSaouter2003.prime_interval_nat_ladder_c05153 n (by omega) (by omega)
            · -- n <= 4782630458643043
              exact RamareSaouter2003.prime_interval_nat_ladder_c05152 n (by omega) (by omega)
          · -- n <= 4769130816340897
            exact RamareSaouter2003.prime_interval_nat_ladder_c05151 n (by omega) (by omega)
