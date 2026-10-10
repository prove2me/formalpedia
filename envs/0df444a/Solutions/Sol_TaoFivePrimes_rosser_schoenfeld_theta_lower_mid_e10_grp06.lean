-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp06
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:40:57.87246+00:00
-- url     : https://prove2.me/submissions/a337f6b8-71c1-4b50-9a25-84fd5dcd58d3

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0251
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0252
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0253
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0254
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0255
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0256
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0257
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0258
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0259
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0260
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0261
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0262
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0263
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0264
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0265
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0266
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0267
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0268
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0269
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0270
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0271
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0272
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0273
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0274
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0275
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0276
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0277
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0278
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0279
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0280
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0281
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0282
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0283
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0284
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0285
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0286
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0287
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0288
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0289
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0290
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0291
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0292
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0293
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0294
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0295
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0296
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0297
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0298
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0299
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0300

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp06` (the range 2594569592 <= n <= 2920492541 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0251` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0300`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (2852721260005778301656 : Real) / 2 ^ 40 <= Chebyshev.theta (2594569592 : Real))
    (n : Nat) (h1 : 2594569592 <= n) (h2 : n <= 2920492541) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3211049915453427999706 : Real) / 2 ^ 40 <= Chebyshev.theta (2920492542 : Real)) := by
  have hb0 := hbase
  have hb1 : (2859868370994453275355 : Real) / 2 ^ 40 <= Chebyshev.theta (2601067412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0251 hb0 2594569592 le_rfl (by norm_num)).2
  have hb2 : (2867016306472803431090 : Real) / 2 ^ 40 <= Chebyshev.theta (2607576510 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0252 hb1 2601067412 le_rfl (by norm_num)).2
  have hb3 : (2874165064604364460997 : Real) / 2 ^ 40 <= Chebyshev.theta (2614077578 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0253 hb2 2607576510 le_rfl (by norm_num)).2
  have hb4 : (2881314642859392826095 : Real) / 2 ^ 40 <= Chebyshev.theta (2620579524 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0254 hb3 2614077578 le_rfl (by norm_num)).2
  have hb5 : (2888465038960263441018 : Real) / 2 ^ 40 <= Chebyshev.theta (2627084774 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0255 hb4 2620579524 le_rfl (by norm_num)).2
  have hb6 : (2895616251441526165061 : Real) / 2 ^ 40 <= Chebyshev.theta (2633588484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0256 hb5 2627084774 le_rfl (by norm_num)).2
  have hb7 : (2902768278748977719239 : Real) / 2 ^ 40 <= Chebyshev.theta (2640099114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0257 hb6 2633588484 le_rfl (by norm_num)).2
  have hb8 : (2909921118972658010315 : Real) / 2 ^ 40 <= Chebyshev.theta (2646611484 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0258 hb7 2640099114 le_rfl (by norm_num)).2
  have hb9 : (2917074770235354434232 : Real) / 2 ^ 40 <= Chebyshev.theta (2653123658 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0259 hb8 2646611484 le_rfl (by norm_num)).2
  have hb10 : (2924229229697896892337 : Real) / 2 ^ 40 <= Chebyshev.theta (2659621932 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0260 hb9 2653123658 le_rfl (by norm_num)).2
  have hb11 : (2931384496190679038202 : Real) / 2 ^ 40 <= Chebyshev.theta (2666134502 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0261 hb10 2659621932 le_rfl (by norm_num)).2
  have hb12 : (2938540567550691998581 : Real) / 2 ^ 40 <= Chebyshev.theta (2672642538 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0262 hb11 2666134502 le_rfl (by norm_num)).2
  have hb13 : (2945697441476680397621 : Real) / 2 ^ 40 <= Chebyshev.theta (2679146444 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0263 hb12 2672642538 le_rfl (by norm_num)).2
  have hb14 : (2952855116279171498199 : Real) / 2 ^ 40 <= Chebyshev.theta (2685664292 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0264 hb13 2679146444 le_rfl (by norm_num)).2
  have hb15 : (2960013590341816218001 : Real) / 2 ^ 40 <= Chebyshev.theta (2692165668 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0265 hb14 2685664292 le_rfl (by norm_num)).2
  have hb16 : (2967172861506257315768 : Real) / 2 ^ 40 <= Chebyshev.theta (2698673400 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0266 hb15 2692165668 le_rfl (by norm_num)).2
  have hb17 : (2974332927765408622408 : Real) / 2 ^ 40 <= Chebyshev.theta (2705186802 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0267 hb16 2698673400 le_rfl (by norm_num)).2
  have hb18 : (2981493787695684685087 : Real) / 2 ^ 40 <= Chebyshev.theta (2711697602 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0268 hb17 2705186802 le_rfl (by norm_num)).2
  have hb19 : (2988655439394381956466 : Real) / 2 ^ 40 <= Chebyshev.theta (2718211092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0269 hb18 2711697602 le_rfl (by norm_num)).2
  have hb20 : (2995817881376885572061 : Real) / 2 ^ 40 <= Chebyshev.theta (2724733070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0270 hb19 2718211092 le_rfl (by norm_num)).2
  have hb21 : (3002981112548573493051 : Real) / 2 ^ 40 <= Chebyshev.theta (2731256150 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0271 hb20 2724733070 le_rfl (by norm_num)).2
  have hb22 : (3010145130784208097913 : Real) / 2 ^ 40 <= Chebyshev.theta (2737773180 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0272 hb21 2731256150 le_rfl (by norm_num)).2
  have hb23 : (3017309933565767960270 : Real) / 2 ^ 40 <= Chebyshev.theta (2744290478 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0273 hb22 2737773180 le_rfl (by norm_num)).2
  have hb24 : (3024475520186763214169 : Real) / 2 ^ 40 <= Chebyshev.theta (2750813078 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0274 hb23 2744290478 le_rfl (by norm_num)).2
  have hb25 : (3031641888144987981983 : Real) / 2 ^ 40 <= Chebyshev.theta (2757325794 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0275 hb24 2750813078 le_rfl (by norm_num)).2
  have hb26 : (3038809035557089505434 : Real) / 2 ^ 40 <= Chebyshev.theta (2763850212 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0276 hb25 2757325794 le_rfl (by norm_num)).2
  have hb27 : (3045976961000412658085 : Real) / 2 ^ 40 <= Chebyshev.theta (2770372110 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0277 hb26 2763850212 le_rfl (by norm_num)).2
  have hb28 : (3053145661594294783971 : Real) / 2 ^ 40 <= Chebyshev.theta (2776883828 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0278 hb27 2770372110 le_rfl (by norm_num)).2
  have hb29 : (3060315136081492790059 : Real) / 2 ^ 40 <= Chebyshev.theta (2783403408 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0279 hb28 2776883828 le_rfl (by norm_num)).2
  have hb30 : (3067485383083449021134 : Real) / 2 ^ 40 <= Chebyshev.theta (2789925770 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0280 hb29 2783403408 le_rfl (by norm_num)).2
  have hb31 : (3074656400867151464688 : Real) / 2 ^ 40 <= Chebyshev.theta (2796449220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0281 hb30 2789925770 le_rfl (by norm_num)).2
  have hb32 : (3081828187641535741034 : Real) / 2 ^ 40 <= Chebyshev.theta (2802968622 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0282 hb31 2796449220 le_rfl (by norm_num)).2
  have hb33 : (3089000741096973536744 : Real) / 2 ^ 40 <= Chebyshev.theta (2809490990 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0283 hb32 2802968622 le_rfl (by norm_num)).2
  have hb34 : (3096174060462968529745 : Real) / 2 ^ 40 <= Chebyshev.theta (2816014808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0284 hb33 2809490990 le_rfl (by norm_num)).2
  have hb35 : (3103348143315090129208 : Real) / 2 ^ 40 <= Chebyshev.theta (2822534480 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0285 hb34 2816014808 le_rfl (by norm_num)).2
  have hb36 : (3110522987723097126441 : Real) / 2 ^ 40 <= Chebyshev.theta (2829060540 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0286 hb35 2822534480 le_rfl (by norm_num)).2
  have hb37 : (3117698592838717912572 : Real) / 2 ^ 40 <= Chebyshev.theta (2835588264 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0287 hb36 2829060540 le_rfl (by norm_num)).2
  have hb38 : (3124874957231110488871 : Real) / 2 ^ 40 <= Chebyshev.theta (2842118688 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0288 hb37 2835588264 le_rfl (by norm_num)).2
  have hb39 : (3132052079120746522974 : Real) / 2 ^ 40 <= Chebyshev.theta (2848648442 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0289 hb38 2842118688 le_rfl (by norm_num)).2
  have hb40 : (3139229956235955018455 : Real) / 2 ^ 40 <= Chebyshev.theta (2855168748 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0290 hb39 2848648442 le_rfl (by norm_num)).2
  have hb41 : (3146408586696546326786 : Real) / 2 ^ 40 <= Chebyshev.theta (2861693070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0291 hb40 2855168748 le_rfl (by norm_num)).2
  have hb42 : (3153587968953154866246 : Real) / 2 ^ 40 <= Chebyshev.theta (2868222290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0292 hb41 2861693070 le_rfl (by norm_num)).2
  have hb43 : (3160768101684345022401 : Real) / 2 ^ 40 <= Chebyshev.theta (2874749540 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0293 hb42 2868222290 le_rfl (by norm_num)).2
  have hb44 : (3167948983526258297110 : Real) / 2 ^ 40 <= Chebyshev.theta (2881283412 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0294 hb43 2874749540 le_rfl (by norm_num)).2
  have hb45 : (3175130612710158144217 : Real) / 2 ^ 40 <= Chebyshev.theta (2887818758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0295 hb44 2881283412 le_rfl (by norm_num)).2
  have hb46 : (3182312988052855451897 : Real) / 2 ^ 40 <= Chebyshev.theta (2894355408 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0296 hb45 2887818758 le_rfl (by norm_num)).2
  have hb47 : (3189496107731468677682 : Real) / 2 ^ 40 <= Chebyshev.theta (2900886518 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0297 hb46 2894355408 le_rfl (by norm_num)).2
  have hb48 : (3196679969635831487682 : Real) / 2 ^ 40 <= Chebyshev.theta (2907416522 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0298 hb47 2900886518 le_rfl (by norm_num)).2
  have hb49 : (3203864572663507101340 : Real) / 2 ^ 40 <= Chebyshev.theta (2913957590 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0299 hb48 2907416522 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0300 hb49 2913957590 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 2757325794 with hc25 | hc25
  · rcases Nat.lt_or_ge n 2672642538 with hc12 | hc12
    · rcases Nat.lt_or_ge n 2633588484 with hc6 | hc6
      · rcases Nat.lt_or_ge n 2614077578 with hc3 | hc3
        · rcases Nat.lt_or_ge n 2601067412 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0251 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2607576510 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0252 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0253 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2620579524 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0254 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2627084774 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0255 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0256 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2653123658 with hc9 | hc9
        · rcases Nat.lt_or_ge n 2640099114 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0257 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2646611484 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0258 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0259 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2659621932 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0260 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2666134502 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0261 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0262 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2711697602 with hc18 | hc18
      · rcases Nat.lt_or_ge n 2692165668 with hc15 | hc15
        · rcases Nat.lt_or_ge n 2679146444 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0263 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2685664292 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0264 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0265 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2698673400 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0266 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2705186802 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0267 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0268 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2731256150 with hc21 | hc21
        · rcases Nat.lt_or_ge n 2718211092 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0269 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2724733070 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0270 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0271 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2744290478 with hc23 | hc23
          · rcases Nat.lt_or_ge n 2737773180 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0272 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0273 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2750813078 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0274 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0275 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 2835588264 with hc37 | hc37
    · rcases Nat.lt_or_ge n 2796449220 with hc31 | hc31
      · rcases Nat.lt_or_ge n 2776883828 with hc28 | hc28
        · rcases Nat.lt_or_ge n 2763850212 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0276 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2770372110 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0277 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0278 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2783403408 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0279 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2789925770 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0280 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0281 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2816014808 with hc34 | hc34
        · rcases Nat.lt_or_ge n 2802968622 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0282 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2809490990 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0283 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0284 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2822534480 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0285 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2829060540 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0286 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0287 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2874749540 with hc43 | hc43
      · rcases Nat.lt_or_ge n 2855168748 with hc40 | hc40
        · rcases Nat.lt_or_ge n 2842118688 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0288 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2848648442 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0289 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0290 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2861693070 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0291 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2868222290 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0292 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0293 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2894355408 with hc46 | hc46
        · rcases Nat.lt_or_ge n 2881283412 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0294 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2887818758 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0295 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0296 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2907416522 with hc48 | hc48
          · rcases Nat.lt_or_ge n 2900886518 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0297 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0298 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2913957590 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0299 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0300 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (2852721260005778301656 : Real) / 2 ^ 40 <= Chebyshev.theta (2594569592 : Real))
    (n : Nat) (h1 : 2594569592 <= n) (h2 : n <= 2920492541) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((3211049915453427999706 : Real) / 2 ^ 40 <= Chebyshev.theta (2920492542 : Real)) :=
  TFPLink.blk hbase n h1 h2
