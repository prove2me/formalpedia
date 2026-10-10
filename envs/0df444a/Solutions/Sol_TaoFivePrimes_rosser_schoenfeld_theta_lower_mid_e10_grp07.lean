-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp07
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:44:05.789891+00:00
-- url     : https://prove2.me/submissions/ed115311-59ca-4449-9edd-2bf0c0affa10

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0301
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0302
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0303
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0304
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0305
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0306
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0307
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0308
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0309
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0310
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0311
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0312
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0313
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0314
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0315
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0316
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0317
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0318
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0319
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0320
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0321
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0322
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0323
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0324
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0325
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0326
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0327
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0328
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0329
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0330
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0331
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0332
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0333
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0334
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0335
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0336
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0337
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0338
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0339
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0340
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0341
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0342
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0343
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0344
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0345
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0346
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0347
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0348
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0349
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0350

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp07` (the range 2920492542 <= n <= 3248089459 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0301` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0350`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (3211049915453427999706 : Real) / 2 ^ 40 <= Chebyshev.theta (2920492542 : Real))
    (n : Nat) (h1 : 2920492542 <= n) (h2 : n <= 3248089459) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3571226616548090907563 : Real) / 2 ^ 40 <= Chebyshev.theta (3248089460 : Real)) := by
  have hb0 := hbase
  have hb1 : (3218235995853563161021 : Real) / 2 ^ 40 <= Chebyshev.theta (2927023098 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0301 hb0 2920492542 le_rfl (by norm_num)).2
  have hb2 : (3225422812024657298228 : Real) / 2 ^ 40 <= Chebyshev.theta (2933559954 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0302 hb1 2927023098 le_rfl (by norm_num)).2
  have hb3 : (3232610363051269236586 : Real) / 2 ^ 40 <= Chebyshev.theta (2940097068 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0303 hb2 2933559954 le_rfl (by norm_num)).2
  have hb4 : (3239798646708430364804 : Real) / 2 ^ 40 <= Chebyshev.theta (2946635808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0304 hb3 2940097068 le_rfl (by norm_num)).2
  have hb5 : (3246987661862444935382 : Real) / 2 ^ 40 <= Chebyshev.theta (2953168634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0305 hb4 2946635808 le_rfl (by norm_num)).2
  have hb6 : (3254177407798822275351 : Real) / 2 ^ 40 <= Chebyshev.theta (2959717854 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0306 hb5 2953168634 le_rfl (by norm_num)).2
  have hb7 : (3261367882318084716699 : Real) / 2 ^ 40 <= Chebyshev.theta (2966253288 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0307 hb6 2959717854 le_rfl (by norm_num)).2
  have hb8 : (3268559083657077671653 : Real) / 2 ^ 40 <= Chebyshev.theta (2972801022 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0308 hb7 2966253288 le_rfl (by norm_num)).2
  have hb9 : (3275751010862774779029 : Real) / 2 ^ 40 <= Chebyshev.theta (2979338192 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0309 hb8 2972801022 le_rfl (by norm_num)).2
  have hb10 : (3282943661659969802092 : Real) / 2 ^ 40 <= Chebyshev.theta (2985881700 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0310 hb9 2979338192 le_rfl (by norm_num)).2
  have hb11 : (3290137034530370060784 : Real) / 2 ^ 40 <= Chebyshev.theta (2992415690 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0311 hb10 2985881700 le_rfl (by norm_num)).2
  have hb12 : (3297331128401123153975 : Real) / 2 ^ 40 <= Chebyshev.theta (2998973610 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0312 hb11 2992415690 le_rfl (by norm_num)).2
  have hb13 : (3304525942848372375148 : Real) / 2 ^ 40 <= Chebyshev.theta (3005518434 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0313 hb12 2998973610 le_rfl (by norm_num)).2
  have hb14 : (3311721475617750798864 : Real) / 2 ^ 40 <= Chebyshev.theta (3012067508 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0314 hb13 3005518434 le_rfl (by norm_num)).2
  have hb15 : (3318917724458240674712 : Real) / 2 ^ 40 <= Chebyshev.theta (3018612420 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0315 hb14 3012067508 le_rfl (by norm_num)).2
  have hb16 : (3326114688441376258392 : Real) / 2 ^ 40 <= Chebyshev.theta (3025162320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0316 hb15 3018612420 le_rfl (by norm_num)).2
  have hb17 : (3333312366642413111191 : Real) / 2 ^ 40 <= Chebyshev.theta (3031711394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0317 hb16 3025162320 le_rfl (by norm_num)).2
  have hb18 : (3340510756382941535874 : Real) / 2 ^ 40 <= Chebyshev.theta (3038254568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0318 hb17 3031711394 le_rfl (by norm_num)).2
  have hb19 : (3347709856277333396608 : Real) / 2 ^ 40 <= Chebyshev.theta (3044797388 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0319 hb18 3038254568 le_rfl (by norm_num)).2
  have hb20 : (3354909664911492569809 : Real) / 2 ^ 40 <= Chebyshev.theta (3051348458 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0320 hb19 3044797388 le_rfl (by norm_num)).2
  have hb21 : (3362110181202705194538 : Real) / 2 ^ 40 <= Chebyshev.theta (3057894108 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0321 hb20 3051348458 le_rfl (by norm_num)).2
  have hb22 : (3369311403613327801677 : Real) / 2 ^ 40 <= Chebyshev.theta (3064442768 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0322 hb21 3057894108 le_rfl (by norm_num)).2
  have hb23 : (3376513329910763103478 : Real) / 2 ^ 40 <= Chebyshev.theta (3070987308 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0323 hb22 3064442768 le_rfl (by norm_num)).2
  have hb24 : (3383715958793112339847 : Real) / 2 ^ 40 <= Chebyshev.theta (3077532840 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0324 hb23 3070987308 le_rfl (by norm_num)).2
  have hb25 : (3390919289524859461241 : Real) / 2 ^ 40 <= Chebyshev.theta (3084085982 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0325 hb24 3077532840 le_rfl (by norm_num)).2
  have hb26 : (3398123320724655833253 : Real) / 2 ^ 40 <= Chebyshev.theta (3090638334 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0326 hb25 3084085982 le_rfl (by norm_num)).2
  have hb27 : (3405328051456034904568 : Real) / 2 ^ 40 <= Chebyshev.theta (3097195422 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0327 hb26 3090638334 le_rfl (by norm_num)).2
  have hb28 : (3412533480500641225550 : Real) / 2 ^ 40 <= Chebyshev.theta (3103760510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0328 hb27 3097195422 le_rfl (by norm_num)).2
  have hb29 : (3419739606410886922321 : Real) / 2 ^ 40 <= Chebyshev.theta (3110314262 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0329 hb28 3103760510 le_rfl (by norm_num)).2
  have hb30 : (3426946427005528724251 : Real) / 2 ^ 40 <= Chebyshev.theta (3116871480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0330 hb29 3110314262 le_rfl (by norm_num)).2
  have hb31 : (3434153940797160787666 : Real) / 2 ^ 40 <= Chebyshev.theta (3123422384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0331 hb30 3116871480 le_rfl (by norm_num)).2
  have hb32 : (3441362145920106555832 : Real) / 2 ^ 40 <= Chebyshev.theta (3129970202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0332 hb31 3123422384 le_rfl (by norm_num)).2
  have hb33 : (3448571041817844778007 : Real) / 2 ^ 40 <= Chebyshev.theta (3136534790 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0333 hb32 3129970202 le_rfl (by norm_num)).2
  have hb34 : (3455780627267554437850 : Real) / 2 ^ 40 <= Chebyshev.theta (3143089922 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0334 hb33 3136534790 le_rfl (by norm_num)).2
  have hb35 : (3462990900627395509768 : Real) / 2 ^ 40 <= Chebyshev.theta (3149648172 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0335 hb34 3143089922 le_rfl (by norm_num)).2
  have hb36 : (3470201859971220221216 : Real) / 2 ^ 40 <= Chebyshev.theta (3156201092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0336 hb35 3149648172 le_rfl (by norm_num)).2
  have hb37 : (3477413504163286106621 : Real) / 2 ^ 40 <= Chebyshev.theta (3162764028 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0337 hb36 3156201092 le_rfl (by norm_num)).2
  have hb38 : (3484625831934255829787 : Real) / 2 ^ 40 <= Chebyshev.theta (3169318320 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0338 hb37 3162764028 le_rfl (by norm_num)).2
  have hb39 : (3491838842099079626094 : Real) / 2 ^ 40 <= Chebyshev.theta (3175883892 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0339 hb38 3169318320 le_rfl (by norm_num)).2
  have hb40 : (3499052533725942576213 : Real) / 2 ^ 40 <= Chebyshev.theta (3182445504 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0340 hb39 3175883892 le_rfl (by norm_num)).2
  have hb41 : (3506266905202030838140 : Real) / 2 ^ 40 <= Chebyshev.theta (3189001394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0341 hb40 3182445504 le_rfl (by norm_num)).2
  have hb42 : (3513481954854059354060 : Real) / 2 ^ 40 <= Chebyshev.theta (3195566208 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0342 hb41 3189001394 le_rfl (by norm_num)).2
  have hb43 : (3520697681759702533894 : Real) / 2 ^ 40 <= Chebyshev.theta (3202130964 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0343 hb42 3195566208 le_rfl (by norm_num)).2
  have hb44 : (3527914083879312784651 : Real) / 2 ^ 40 <= Chebyshev.theta (3208682288 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0344 hb43 3202130964 le_rfl (by norm_num)).2
  have hb45 : (3535131160104871367391 : Real) / 2 ^ 40 <= Chebyshev.theta (3215251058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0345 hb44 3208682288 le_rfl (by norm_num)).2
  have hb46 : (3542348909877252117461 : Real) / 2 ^ 40 <= Chebyshev.theta (3221821412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0346 hb45 3215251058 le_rfl (by norm_num)).2
  have hb47 : (3549567331818827706043 : Real) / 2 ^ 40 <= Chebyshev.theta (3228389502 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0347 hb46 3221821412 le_rfl (by norm_num)).2
  have hb48 : (3556786424542109344509 : Real) / 2 ^ 40 <= Chebyshev.theta (3234954792 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0348 hb47 3228389502 le_rfl (by norm_num)).2
  have hb49 : (3564006186455494632710 : Real) / 2 ^ 40 <= Chebyshev.theta (3241525212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0349 hb48 3234954792 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0350 hb49 3241525212 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 3084085982 with hc25 | hc25
  · rcases Nat.lt_or_ge n 2998973610 with hc12 | hc12
    · rcases Nat.lt_or_ge n 2959717854 with hc6 | hc6
      · rcases Nat.lt_or_ge n 2940097068 with hc3 | hc3
        · rcases Nat.lt_or_ge n 2927023098 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0301 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2933559954 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0302 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0303 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2946635808 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0304 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2953168634 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0305 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0306 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2979338192 with hc9 | hc9
        · rcases Nat.lt_or_ge n 2966253288 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0307 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2972801022 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0308 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0309 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2985881700 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0310 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2992415690 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0311 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0312 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3038254568 with hc18 | hc18
      · rcases Nat.lt_or_ge n 3018612420 with hc15 | hc15
        · rcases Nat.lt_or_ge n 3005518434 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0313 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3012067508 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0314 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0315 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3025162320 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0316 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3031711394 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0317 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0318 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3057894108 with hc21 | hc21
        · rcases Nat.lt_or_ge n 3044797388 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0319 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3051348458 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0320 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0321 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3070987308 with hc23 | hc23
          · rcases Nat.lt_or_ge n 3064442768 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0322 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0323 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3077532840 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0324 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0325 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 3162764028 with hc37 | hc37
    · rcases Nat.lt_or_ge n 3123422384 with hc31 | hc31
      · rcases Nat.lt_or_ge n 3103760510 with hc28 | hc28
        · rcases Nat.lt_or_ge n 3090638334 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0326 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3097195422 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0327 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0328 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3110314262 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0329 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3116871480 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0330 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0331 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3143089922 with hc34 | hc34
        · rcases Nat.lt_or_ge n 3129970202 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0332 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3136534790 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0333 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0334 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3149648172 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0335 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3156201092 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0336 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0337 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 3202130964 with hc43 | hc43
      · rcases Nat.lt_or_ge n 3182445504 with hc40 | hc40
        · rcases Nat.lt_or_ge n 3169318320 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0338 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3175883892 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0339 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0340 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3189001394 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0341 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3195566208 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0342 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0343 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 3221821412 with hc46 | hc46
        · rcases Nat.lt_or_ge n 3208682288 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0344 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3215251058 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0345 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0346 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 3234954792 with hc48 | hc48
          · rcases Nat.lt_or_ge n 3228389502 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0347 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0348 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 3241525212 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0349 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0350 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (3211049915453427999706 : Real) / 2 ^ 40 <= Chebyshev.theta (2920492542 : Real))
    (n : Nat) (h1 : 2920492542 <= n) (h2 : n <= 3248089459) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3571226616548090907563 : Real) / 2 ^ 40 <= Chebyshev.theta (3248089460 : Real)) :=
  TFPLink.blk hbase n h1 h2
