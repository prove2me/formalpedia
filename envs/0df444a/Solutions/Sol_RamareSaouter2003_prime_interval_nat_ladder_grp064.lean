-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp064
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T02:46:59.810663+00:00
-- url     : https://prove2.me/submissions/44e8edc3-ddee-4e20-8c11-941ba306f688

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c03200

theorem solution (n : Nat)
    (hn : 21984887510237 < n) (hupper : n <= 24876889450507) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 23386227061033 n with h2 | h2
  · -- n > 23386227061033
    rcases Nat.lt_or_ge 24090255206153 n with h4 | h4
    · -- n > 24090255206153
      rcases Nat.lt_or_ge 24450177721819 n with h6 | h6
      · -- n > 24450177721819
        rcases Nat.lt_or_ge 24632150531011 n with h8 | h8
        · -- n > 24632150531011
          rcases Nat.lt_or_ge 24754217533237 n with h10 | h10
          · -- n > 24754217533237
            rcases Nat.lt_or_ge 24815477690501 n with h12 | h12
            · -- n > 24815477690501
              exact RamareSaouter2003.prime_interval_nat_ladder_c03200 n (by omega) (by omega)
            · -- n <= 24815477690501
              exact RamareSaouter2003.prime_interval_nat_ladder_c03199 n (by omega) (by omega)
          · -- n <= 24754217533237
            rcases Nat.lt_or_ge 24693108604621 n with h12 | h12
            · -- n > 24693108604621
              exact RamareSaouter2003.prime_interval_nat_ladder_c03198 n (by omega) (by omega)
            · -- n <= 24693108604621
              exact RamareSaouter2003.prime_interval_nat_ladder_c03197 n (by omega) (by omega)
        · -- n <= 24632150531011
          rcases Nat.lt_or_ge 24510685460593 n with h10 | h10
          · -- n > 24510685460593
            rcases Nat.lt_or_ge 24571342940119 n with h12 | h12
            · -- n > 24571342940119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03196 n (by omega) (by omega)
            · -- n <= 24571342940119
              exact RamareSaouter2003.prime_interval_nat_ladder_c03195 n (by omega) (by omega)
          · -- n <= 24510685460593
            exact RamareSaouter2003.prime_interval_nat_ladder_c03194 n (by omega) (by omega)
      · -- n <= 24450177721819
        rcases Nat.lt_or_ge 24269549257501 n with h8 | h8
        · -- n > 24269549257501
          rcases Nat.lt_or_ge 24329609988547 n with h10 | h10
          · -- n > 24329609988547
            rcases Nat.lt_or_ge 24389819353891 n with h12 | h12
            · -- n > 24389819353891
              exact RamareSaouter2003.prime_interval_nat_ladder_c03193 n (by omega) (by omega)
            · -- n <= 24389819353891
              exact RamareSaouter2003.prime_interval_nat_ladder_c03192 n (by omega) (by omega)
          · -- n <= 24329609988547
            exact RamareSaouter2003.prime_interval_nat_ladder_c03191 n (by omega) (by omega)
        · -- n <= 24269549257501
          rcases Nat.lt_or_ge 24149872231847 n with h10 | h10
          · -- n > 24149872231847
            rcases Nat.lt_or_ge 24209636793877 n with h12 | h12
            · -- n > 24209636793877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03190 n (by omega) (by omega)
            · -- n <= 24209636793877
              exact RamareSaouter2003.prime_interval_nat_ladder_c03189 n (by omega) (by omega)
          · -- n <= 24149872231847
            exact RamareSaouter2003.prime_interval_nat_ladder_c03188 n (by omega) (by omega)
    · -- n <= 24090255206153
      rcases Nat.lt_or_ge 23735630984183 n with h6 | h6
      · -- n > 23735630984183
        rcases Nat.lt_or_ge 23912285710457 n with h8 | h8
        · -- n > 23912285710457
          rcases Nat.lt_or_ge 23971462308281 n with h10 | h10
          · -- n > 23971462308281
            rcases Nat.lt_or_ge 24030785352653 n with h12 | h12
            · -- n > 24030785352653
              exact RamareSaouter2003.prime_interval_nat_ladder_c03187 n (by omega) (by omega)
            · -- n <= 24030785352653
              exact RamareSaouter2003.prime_interval_nat_ladder_c03186 n (by omega) (by omega)
          · -- n <= 23971462308281
            exact RamareSaouter2003.prime_interval_nat_ladder_c03185 n (by omega) (by omega)
        · -- n <= 23912285710457
          rcases Nat.lt_or_ge 23794370408491 n with h10 | h10
          · -- n > 23794370408491
            rcases Nat.lt_or_ge 23853255197281 n with h12 | h12
            · -- n > 23853255197281
              exact RamareSaouter2003.prime_interval_nat_ladder_c03184 n (by omega) (by omega)
            · -- n <= 23853255197281
              exact RamareSaouter2003.prime_interval_nat_ladder_c03183 n (by omega) (by omega)
          · -- n <= 23794370408491
            exact RamareSaouter2003.prime_interval_nat_ladder_c03182 n (by omega) (by omega)
      · -- n <= 23735630984183
        rcases Nat.lt_or_ge 23560281314813 n with h8 | h8
        · -- n > 23560281314813
          rcases Nat.lt_or_ge 23618586794903 n with h10 | h10
          · -- n > 23618586794903
            rcases Nat.lt_or_ge 23677036565647 n with h12 | h12
            · -- n > 23677036565647
              exact RamareSaouter2003.prime_interval_nat_ladder_c03181 n (by omega) (by omega)
            · -- n <= 23677036565647
              exact RamareSaouter2003.prime_interval_nat_ladder_c03180 n (by omega) (by omega)
          · -- n <= 23618586794903
            exact RamareSaouter2003.prime_interval_nat_ladder_c03179 n (by omega) (by omega)
        · -- n <= 23560281314813
          rcases Nat.lt_or_ge 23444101802783 n with h10 | h10
          · -- n > 23444101802783
            rcases Nat.lt_or_ge 23502119769229 n with h12 | h12
            · -- n > 23502119769229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03178 n (by omega) (by omega)
            · -- n <= 23502119769229
              exact RamareSaouter2003.prime_interval_nat_ladder_c03177 n (by omega) (by omega)
          · -- n <= 23444101802783
            exact RamareSaouter2003.prime_interval_nat_ladder_c03176 n (by omega) (by omega)
  · -- n <= 23386227061033
    rcases Nat.lt_or_ge 22646729179891 n with h4 | h4
    · -- n > 22646729179891
      rcases Nat.lt_or_ge 22985084571019 n with h6 | h6
      · -- n > 22985084571019
        rcases Nat.lt_or_ge 23156153282971 n with h8 | h8
        · -- n > 23156153282971
          rcases Nat.lt_or_ge 23270905838293 n with h10 | h10
          · -- n > 23270905838293
            rcases Nat.lt_or_ge 23328495190447 n with h12 | h12
            · -- n > 23328495190447
              exact RamareSaouter2003.prime_interval_nat_ladder_c03175 n (by omega) (by omega)
            · -- n <= 23328495190447
              exact RamareSaouter2003.prime_interval_nat_ladder_c03174 n (by omega) (by omega)
          · -- n <= 23270905838293
            rcases Nat.lt_or_ge 23213458652771 n with h12 | h12
            · -- n > 23213458652771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03173 n (by omega) (by omega)
            · -- n <= 23213458652771
              exact RamareSaouter2003.prime_interval_nat_ladder_c03172 n (by omega) (by omega)
        · -- n <= 23156153282971
          rcases Nat.lt_or_ge 23041966590941 n with h10 | h10
          · -- n > 23041966590941
            rcases Nat.lt_or_ge 23098989378833 n with h12 | h12
            · -- n > 23098989378833
              exact RamareSaouter2003.prime_interval_nat_ladder_c03171 n (by omega) (by omega)
            · -- n <= 23098989378833
              exact RamareSaouter2003.prime_interval_nat_ladder_c03170 n (by omega) (by omega)
          · -- n <= 23041966590941
            exact RamareSaouter2003.prime_interval_nat_ladder_c03169 n (by omega) (by omega)
      · -- n <= 22985084571019
        rcases Nat.lt_or_ge 22815279649181 n with h8 | h8
        · -- n > 22815279649181
          rcases Nat.lt_or_ge 22871741446601 n with h10 | h10
          · -- n > 22871741446601
            rcases Nat.lt_or_ge 22928342971879 n with h12 | h12
            · -- n > 22928342971879
              exact RamareSaouter2003.prime_interval_nat_ladder_c03168 n (by omega) (by omega)
            · -- n <= 22928342971879
              exact RamareSaouter2003.prime_interval_nat_ladder_c03167 n (by omega) (by omega)
          · -- n <= 22871741446601
            exact RamareSaouter2003.prime_interval_nat_ladder_c03166 n (by omega) (by omega)
        · -- n <= 22815279649181
          rcases Nat.lt_or_ge 22702773859523 n with h10 | h10
          · -- n > 22702773859523
            rcases Nat.lt_or_ge 22758957234919 n with h12 | h12
            · -- n > 22758957234919
              exact RamareSaouter2003.prime_interval_nat_ladder_c03165 n (by omega) (by omega)
            · -- n <= 22758957234919
              exact RamareSaouter2003.prime_interval_nat_ladder_c03164 n (by omega) (by omega)
          · -- n <= 22702773859523
            exact RamareSaouter2003.prime_interval_nat_ladder_c03163 n (by omega) (by omega)
    · -- n <= 22646729179891
      rcases Nat.lt_or_ge 22313354600083 n with h6 | h6
      · -- n > 22313354600083
        rcases Nat.lt_or_ge 22479423896201 n with h8 | h8
        · -- n > 22479423896201
          rcases Nat.lt_or_ge 22535054539363 n with h10 | h10
          · -- n > 22535054539363
            rcases Nat.lt_or_ge 22590822853691 n with h12 | h12
            · -- n > 22590822853691
              exact RamareSaouter2003.prime_interval_nat_ladder_c03162 n (by omega) (by omega)
            · -- n <= 22590822853691
              exact RamareSaouter2003.prime_interval_nat_ladder_c03161 n (by omega) (by omega)
          · -- n <= 22535054539363
            exact RamareSaouter2003.prime_interval_nat_ladder_c03160 n (by omega) (by omega)
        · -- n <= 22479423896201
          rcases Nat.lt_or_ge 22368574265203 n with h10 | h10
          · -- n > 22368574265203
            rcases Nat.lt_or_ge 22423930584659 n with h12 | h12
            · -- n > 22423930584659
              exact RamareSaouter2003.prime_interval_nat_ladder_c03159 n (by omega) (by omega)
            · -- n <= 22423930584659
              exact RamareSaouter2003.prime_interval_nat_ladder_c03158 n (by omega) (by omega)
          · -- n <= 22368574265203
            exact RamareSaouter2003.prime_interval_nat_ladder_c03157 n (by omega) (by omega)
      · -- n <= 22313354600083
        rcases Nat.lt_or_ge 22148512159097 n with h8 | h8
        · -- n > 22148512159097
          rcases Nat.lt_or_ge 22203323882933 n with h10 | h10
          · -- n > 22203323882933
            rcases Nat.lt_or_ge 22258271251331 n with h12 | h12
            · -- n > 22258271251331
              exact RamareSaouter2003.prime_interval_nat_ladder_c03156 n (by omega) (by omega)
            · -- n <= 22258271251331
              exact RamareSaouter2003.prime_interval_nat_ladder_c03155 n (by omega) (by omega)
          · -- n <= 22203323882933
            exact RamareSaouter2003.prime_interval_nat_ladder_c03154 n (by omega) (by omega)
        · -- n <= 22148512159097
          rcases Nat.lt_or_ge 22039294306333 n with h10 | h10
          · -- n > 22039294306333
            rcases Nat.lt_or_ge 22093835744927 n with h12 | h12
            · -- n > 22093835744927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03153 n (by omega) (by omega)
            · -- n <= 22093835744927
              exact RamareSaouter2003.prime_interval_nat_ladder_c03152 n (by omega) (by omega)
          · -- n <= 22039294306333
            exact RamareSaouter2003.prime_interval_nat_ladder_c03151 n (by omega) (by omega)
