-- Prove2me | solution 1 for RamareSaouter2003.prime_interval_nat_ladder_grp084
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-12T09:30:12.776166+00:00
-- url     : https://prove2.me/submissions/8e8eb14d-16c3-4dcf-a4cf-b25d5fce1057

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Real.Basic
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04151
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04152
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04153
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04154
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04155
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04156
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04157
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04158
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04159
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04160
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04161
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04162
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04163
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04164
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04165
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04166
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04167
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04168
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04169
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04170
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04171
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04172
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04173
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04174
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04175
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04176
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04177
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04178
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04179
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04180
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04181
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04182
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04183
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04184
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04185
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04186
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04187
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04188
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04189
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04190
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04191
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04192
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04193
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04194
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04195
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04196
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04197
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04198
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04199
import Theorems.Thm_RamareSaouter2003_prime_interval_nat_ladder_c04200

theorem solution (n : Nat)
    (hn : 281681085386551 < n) (hupper : n <= 324415616742421) :
    Exists fun p : Nat => p.Prime /\
      (n : Real) * (1 - 1 / 28314000) < (p : Real) /\ (p : Real) < (n : Real) := by
  rcases Nat.lt_or_ge 302296547621899 n with h2 | h2
  · -- n > 302296547621899
    rcases Nat.lt_or_ge 312717535159273 n with h4 | h4
    · -- n > 312717535159273
      rcases Nat.lt_or_ge 318064976405611 n with h6 | h6
      · -- n > 318064976405611
        rcases Nat.lt_or_ge 320770615405327 n with h8 | h8
        · -- n > 320770615405327
          rcases Nat.lt_or_ge 322587759120629 n with h10 | h10
          · -- n > 322587759120629
            rcases Nat.lt_or_ge 323501024574443 n with h12 | h12
            · -- n > 323501024574443
              exact RamareSaouter2003.prime_interval_nat_ladder_c04200 n (by omega) (by omega)
            · -- n <= 323501024574443
              exact RamareSaouter2003.prime_interval_nat_ladder_c04199 n (by omega) (by omega)
          · -- n <= 322587759120629
            rcases Nat.lt_or_ge 321677539637947 n with h12 | h12
            · -- n > 321677539637947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04198 n (by omega) (by omega)
            · -- n <= 321677539637947
              exact RamareSaouter2003.prime_interval_nat_ladder_c04197 n (by omega) (by omega)
        · -- n <= 320770615405327
          rcases Nat.lt_or_ge 318965214349979 n with h10 | h10
          · -- n > 318965214349979
            rcases Nat.lt_or_ge 319867080716459 n with h12 | h12
            · -- n > 319867080716459
              exact RamareSaouter2003.prime_interval_nat_ladder_c04196 n (by omega) (by omega)
            · -- n <= 319867080716459
              exact RamareSaouter2003.prime_interval_nat_ladder_c04195 n (by omega) (by omega)
          · -- n <= 318965214349979
            exact RamareSaouter2003.prime_interval_nat_ladder_c04194 n (by omega) (by omega)
      · -- n <= 318064976405611
        rcases Nat.lt_or_ge 315379675213919 n with h8 | h8
        · -- n > 315379675213919
          rcases Nat.lt_or_ge 316271625628019 n with h10 | h10
          · -- n > 316271625628019
            rcases Nat.lt_or_ge 317167079029967 n with h12 | h12
            · -- n > 317167079029967
              exact RamareSaouter2003.prime_interval_nat_ladder_c04193 n (by omega) (by omega)
            · -- n <= 317167079029967
              exact RamareSaouter2003.prime_interval_nat_ladder_c04192 n (by omega) (by omega)
          · -- n <= 316271625628019
            exact RamareSaouter2003.prime_interval_nat_ladder_c04191 n (by omega) (by omega)
        · -- n <= 315379675213919
          rcases Nat.lt_or_ge 313602456503131 n with h10 | h10
          · -- n > 313602456503131
            rcases Nat.lt_or_ge 314489835684523 n with h12 | h12
            · -- n > 314489835684523
              exact RamareSaouter2003.prime_interval_nat_ladder_c04190 n (by omega) (by omega)
            · -- n <= 314489835684523
              exact RamareSaouter2003.prime_interval_nat_ladder_c04189 n (by omega) (by omega)
          · -- n <= 313602456503131
            exact RamareSaouter2003.prime_interval_nat_ladder_c04188 n (by omega) (by omega)
    · -- n <= 312717535159273
      rcases Nat.lt_or_ge 307462873752257 n with h6 | h6
      · -- n > 307462873752257
        rcases Nat.lt_or_ge 310078510247591 n with h8 | h8
        · -- n > 310078510247591
          rcases Nat.lt_or_ge 310955320655377 n with h10 | h10
          · -- n > 310955320655377
            rcases Nat.lt_or_ge 311834851872931 n with h12 | h12
            · -- n > 311834851872931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04187 n (by omega) (by omega)
            · -- n <= 311834851872931
              exact RamareSaouter2003.prime_interval_nat_ladder_c04186 n (by omega) (by omega)
          · -- n <= 310955320655377
            exact RamareSaouter2003.prime_interval_nat_ladder_c04185 n (by omega) (by omega)
        · -- n <= 310078510247591
          rcases Nat.lt_or_ge 308332853771027 n with h10 | h10
          · -- n > 308332853771027
            rcases Nat.lt_or_ge 309205189220891 n with h12 | h12
            · -- n > 309205189220891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04184 n (by omega) (by omega)
            · -- n <= 309205189220891
              exact RamareSaouter2003.prime_interval_nat_ladder_c04183 n (by omega) (by omega)
          · -- n <= 308332853771027
            exact RamareSaouter2003.prime_interval_nat_ladder_c04182 n (by omega) (by omega)
      · -- n <= 307462873752257
        rcases Nat.lt_or_ge 304869838788149 n with h8 | h8
        · -- n > 304869838788149
          rcases Nat.lt_or_ge 305732894420293 n with h10 | h10
          · -- n > 305732894420293
            rcases Nat.lt_or_ge 306595521703643 n with h12 | h12
            · -- n > 306595521703643
              exact RamareSaouter2003.prime_interval_nat_ladder_c04181 n (by omega) (by omega)
            · -- n <= 306595521703643
              exact RamareSaouter2003.prime_interval_nat_ladder_c04180 n (by omega) (by omega)
          · -- n <= 305732894420293
            exact RamareSaouter2003.prime_interval_nat_ladder_c04179 n (by omega) (by omega)
        · -- n <= 304869838788149
          rcases Nat.lt_or_ge 303152403527639 n with h10 | h10
          · -- n > 303152403527639
            rcases Nat.lt_or_ge 304010270875217 n with h12 | h12
            · -- n > 304010270875217
              exact RamareSaouter2003.prime_interval_nat_ladder_c04178 n (by omega) (by omega)
            · -- n <= 304010270875217
              exact RamareSaouter2003.prime_interval_nat_ladder_c04177 n (by omega) (by omega)
          · -- n <= 303152403527639
            exact RamareSaouter2003.prime_interval_nat_ladder_c04176 n (by omega) (by omega)
  · -- n <= 302296547621899
    rcases Nat.lt_or_ge 291395972951173 n with h4 | h4
    · -- n > 291395972951173
      rcases Nat.lt_or_ge 296377273298321 n with h6 | h6
      · -- n > 296377273298321
        rcases Nat.lt_or_ge 298899781592129 n with h8 | h8
        · -- n > 298899781592129
          rcases Nat.lt_or_ge 300593980123747 n with h10 | h10
          · -- n > 300593980123747
            rcases Nat.lt_or_ge 301444645056827 n with h12 | h12
            · -- n > 301444645056827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04175 n (by omega) (by omega)
            · -- n <= 301444645056827
              exact RamareSaouter2003.prime_interval_nat_ladder_c04174 n (by omega) (by omega)
          · -- n <= 300593980123747
            rcases Nat.lt_or_ge 299745832366831 n with h12 | h12
            · -- n > 299745832366831
              exact RamareSaouter2003.prime_interval_nat_ladder_c04173 n (by omega) (by omega)
            · -- n <= 299745832366831
              exact RamareSaouter2003.prime_interval_nat_ladder_c04172 n (by omega) (by omega)
        · -- n <= 298899781592129
          rcases Nat.lt_or_ge 297214645714717 n with h10 | h10
          · -- n > 297214645714717
            rcases Nat.lt_or_ge 298056031676497 n with h12 | h12
            · -- n > 298056031676497
              exact RamareSaouter2003.prime_interval_nat_ladder_c04171 n (by omega) (by omega)
            · -- n <= 298056031676497
              exact RamareSaouter2003.prime_interval_nat_ladder_c04170 n (by omega) (by omega)
          · -- n <= 297214645714717
            exact RamareSaouter2003.prime_interval_nat_ladder_c04169 n (by omega) (by omega)
      · -- n <= 296377273298321
        rcases Nat.lt_or_ge 293876082686917 n with h8 | h8
        · -- n > 293876082686917
          rcases Nat.lt_or_ge 294707823056893 n with h10 | h10
          · -- n > 294707823056893
            rcases Nat.lt_or_ge 295541803547981 n with h12 | h12
            · -- n > 295541803547981
              exact RamareSaouter2003.prime_interval_nat_ladder_c04168 n (by omega) (by omega)
            · -- n <= 295541803547981
              exact RamareSaouter2003.prime_interval_nat_ladder_c04167 n (by omega) (by omega)
          · -- n <= 294707823056893
            exact RamareSaouter2003.prime_interval_nat_ladder_c04166 n (by omega) (by omega)
        · -- n <= 293876082686917
          rcases Nat.lt_or_ge 292220951045623 n with h10 | h10
          · -- n > 292220951045623
            rcases Nat.lt_or_ge 293047812854123 n with h12 | h12
            · -- n > 293047812854123
              exact RamareSaouter2003.prime_interval_nat_ladder_c04165 n (by omega) (by omega)
            · -- n <= 293047812854123
              exact RamareSaouter2003.prime_interval_nat_ladder_c04164 n (by omega) (by omega)
          · -- n <= 292220951045623
            exact RamareSaouter2003.prime_interval_nat_ladder_c04163 n (by omega) (by omega)
    · -- n <= 291395972951173
      rcases Nat.lt_or_ge 286498154754191 n with h6 | h6
      · -- n > 286498154754191
        rcases Nat.lt_or_ge 288935518279619 n with h8 | h8
        · -- n > 288935518279619
          rcases Nat.lt_or_ge 289753398698033 n with h10 | h10
          · -- n > 289753398698033
            rcases Nat.lt_or_ge 290573729948609 n with h12 | h12
            · -- n > 290573729948609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04162 n (by omega) (by omega)
            · -- n <= 290573729948609
              exact RamareSaouter2003.prime_interval_nat_ladder_c04161 n (by omega) (by omega)
          · -- n <= 289753398698033
            exact RamareSaouter2003.prime_interval_nat_ladder_c04160 n (by omega) (by omega)
        · -- n <= 288935518279619
          rcases Nat.lt_or_ge 287309157304441 n with h10 | h10
          · -- n > 287309157304441
            rcases Nat.lt_or_ge 288119878263331 n with h12 | h12
            · -- n > 288119878263331
              exact RamareSaouter2003.prime_interval_nat_ladder_c04159 n (by omega) (by omega)
            · -- n <= 288119878263331
              exact RamareSaouter2003.prime_interval_nat_ladder_c04158 n (by omega) (by omega)
          · -- n <= 287309157304441
            exact RamareSaouter2003.prime_interval_nat_ladder_c04157 n (by omega) (by omega)
      · -- n <= 286498154754191
        rcases Nat.lt_or_ge 284079306463319 n with h8 | h8
        · -- n > 284079306463319
          rcases Nat.lt_or_ge 284883234882923 n with h10 | h10
          · -- n > 284883234882923
            rcases Nat.lt_or_ge 285689718790339 n with h12 | h12
            · -- n > 285689718790339
              exact RamareSaouter2003.prime_interval_nat_ladder_c04156 n (by omega) (by omega)
            · -- n <= 285689718790339
              exact RamareSaouter2003.prime_interval_nat_ladder_c04155 n (by omega) (by omega)
          · -- n <= 284883234882923
            exact RamareSaouter2003.prime_interval_nat_ladder_c04154 n (by omega) (by omega)
        · -- n <= 284079306463319
          rcases Nat.lt_or_ge 282478085781011 n with h10 | h10
          · -- n > 282478085781011
            rcases Nat.lt_or_ge 283277390021671 n with h12 | h12
            · -- n > 283277390021671
              exact RamareSaouter2003.prime_interval_nat_ladder_c04153 n (by omega) (by omega)
            · -- n <= 283277390021671
              exact RamareSaouter2003.prime_interval_nat_ladder_c04152 n (by omega) (by omega)
          · -- n <= 282478085781011
            exact RamareSaouter2003.prime_interval_nat_ladder_c04151 n (by omega) (by omega)
