-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp05
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:38:00.768475+00:00
-- url     : https://prove2.me/submissions/90b26ffe-b8a4-4706-8bfc-0bfe0446a560

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0201
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0202
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0203
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0204
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0205
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0206
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0207
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0208
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0209
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0210
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0211
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0212
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0213
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0214
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0215
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0216
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0217
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0218
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0219
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0220
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0221
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0222
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0223
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0224
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0225
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0226
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0227
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0228
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0229
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0230
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0231
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0232
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0233
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0234
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0235
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0236
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0237
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0238
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0239
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0240
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0241
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0242
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0243
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0244
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0245
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0246
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0247
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0248
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0249
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0250

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp05` (the range 2270572190 <= n <= 2594569591 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0201` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0250`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (2496462384131083673405 : Real) / 2 ^ 40 <= Chebyshev.theta (2270572190 : Real))
    (n : Nat) (h1 : 2270572190 <= n) (h2 : n <= 2594569591) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2852721260005778301656 : Real) / 2 ^ 40 <= Chebyshev.theta (2594569592 : Real)) := by
  have hb0 := hbase
  have hb1 : (2503565572225959359546 : Real) / 2 ^ 40 <= Chebyshev.theta (2277016902 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0201 hb0 2270572190 le_rfl (by norm_num)).2
  have hb2 : (2510669695855385376626 : Real) / 2 ^ 40 <= Chebyshev.theta (2283491082 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0202 hb1 2277016902 le_rfl (by norm_num)).2
  have hb3 : (2517774752913102761623 : Real) / 2 ^ 40 <= Chebyshev.theta (2289947064 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0203 hb2 2283491082 le_rfl (by norm_num)).2
  have hb4 : (2524880739808609817589 : Real) / 2 ^ 40 <= Chebyshev.theta (2296403384 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0204 hb3 2289947064 le_rfl (by norm_num)).2
  have hb5 : (2531987654187064368198 : Real) / 2 ^ 40 <= Chebyshev.theta (2302871742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0205 hb4 2296403384 le_rfl (by norm_num)).2
  have hb6 : (2539095494666187452647 : Real) / 2 ^ 40 <= Chebyshev.theta (2309338502 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0206 hb5 2302871742 le_rfl (by norm_num)).2
  have hb7 : (2546204257929737595852 : Real) / 2 ^ 40 <= Chebyshev.theta (2315797218 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0207 hb6 2309338502 le_rfl (by norm_num)).2
  have hb8 : (2553313941796099396626 : Real) / 2 ^ 40 <= Chebyshev.theta (2322269708 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0208 hb7 2315797218 le_rfl (by norm_num)).2
  have hb9 : (2560424544052770617399 : Real) / 2 ^ 40 <= Chebyshev.theta (2328740634 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0209 hb8 2322269708 le_rfl (by norm_num)).2
  have hb10 : (2567536062837609941745 : Real) / 2 ^ 40 <= Chebyshev.theta (2335211688 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0210 hb9 2328740634 le_rfl (by norm_num)).2
  have hb11 : (2574648494610167232881 : Real) / 2 ^ 40 <= Chebyshev.theta (2341677698 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0211 hb10 2335211688 le_rfl (by norm_num)).2
  have hb12 : (2581761837574354348576 : Real) / 2 ^ 40 <= Chebyshev.theta (2348153220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0212 hb11 2341677698 le_rfl (by norm_num)).2
  have hb13 : (2588876089378678287533 : Real) / 2 ^ 40 <= Chebyshev.theta (2354623410 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0213 hb12 2348153220 le_rfl (by norm_num)).2
  have hb14 : (2595991247384361257032 : Real) / 2 ^ 40 <= Chebyshev.theta (2361102092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0214 hb13 2354623410 le_rfl (by norm_num)).2
  have hb15 : (2603107309747496338032 : Real) / 2 ^ 40 <= Chebyshev.theta (2367571980 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0215 hb14 2361102092 le_rfl (by norm_num)).2
  have hb16 : (2610224272806877027406 : Real) / 2 ^ 40 <= Chebyshev.theta (2374041764 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0216 hb15 2367571980 le_rfl (by norm_num)).2
  have hb17 : (2617342134974622230594 : Real) / 2 ^ 40 <= Chebyshev.theta (2380519398 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0217 hb16 2374041764 le_rfl (by norm_num)).2
  have hb18 : (2624460893914124168651 : Real) / 2 ^ 40 <= Chebyshev.theta (2386991442 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0218 hb17 2380519398 le_rfl (by norm_num)).2
  have hb19 : (2631580546871988836737 : Real) / 2 ^ 40 <= Chebyshev.theta (2393464394 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0219 hb18 2386991442 le_rfl (by norm_num)).2
  have hb20 : (2638701092253450724951 : Real) / 2 ^ 40 <= Chebyshev.theta (2399943864 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0220 hb19 2393464394 le_rfl (by norm_num)).2
  have hb21 : (2645822528044167118305 : Real) / 2 ^ 40 <= Chebyshev.theta (2406429924 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0221 hb20 2399943864 le_rfl (by norm_num)).2
  have hb22 : (2652944851535585744296 : Real) / 2 ^ 40 <= Chebyshev.theta (2412906648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0222 hb21 2406429924 le_rfl (by norm_num)).2
  have hb23 : (2660068060552417421238 : Real) / 2 ^ 40 <= Chebyshev.theta (2419384532 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0223 hb22 2412906648 le_rfl (by norm_num)).2
  have hb24 : (2667192152206742947269 : Real) / 2 ^ 40 <= Chebyshev.theta (2425860990 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0224 hb23 2419384532 le_rfl (by norm_num)).2
  have hb25 : (2674317123861831247743 : Real) / 2 ^ 40 <= Chebyshev.theta (2432341758 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0225 hb24 2425860990 le_rfl (by norm_num)).2
  have hb26 : (2681442974388824272426 : Real) / 2 ^ 40 <= Chebyshev.theta (2438824338 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0226 hb25 2432341758 le_rfl (by norm_num)).2
  have hb27 : (2688569700556884509487 : Real) / 2 ^ 40 <= Chebyshev.theta (2445300450 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0227 hb26 2438824338 le_rfl (by norm_num)).2
  have hb28 : (2695697300996013306564 : Real) / 2 ^ 40 <= Chebyshev.theta (2451791540 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0228 hb27 2445300450 le_rfl (by norm_num)).2
  have hb29 : (2702825773417049530966 : Real) / 2 ^ 40 <= Chebyshev.theta (2458270044 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0229 hb28 2451791540 le_rfl (by norm_num)).2
  have hb30 : (2709955115806208663542 : Real) / 2 ^ 40 <= Chebyshev.theta (2464764374 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0230 hb29 2458270044 le_rfl (by norm_num)).2
  have hb31 : (2717085325980944976708 : Real) / 2 ^ 40 <= Chebyshev.theta (2471245500 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0231 hb30 2464764374 le_rfl (by norm_num)).2
  have hb32 : (2724216400429276321431 : Real) / 2 ^ 40 <= Chebyshev.theta (2477724678 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0232 hb31 2471245500 le_rfl (by norm_num)).2
  have hb33 : (2731348337303016277243 : Real) / 2 ^ 40 <= Chebyshev.theta (2484206694 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0233 hb32 2477724678 le_rfl (by norm_num)).2
  have hb34 : (2738481135265844007356 : Real) / 2 ^ 40 <= Chebyshev.theta (2490701444 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0234 hb33 2484206694 le_rfl (by norm_num)).2
  have hb35 : (2745614792931201049541 : Real) / 2 ^ 40 <= Chebyshev.theta (2497192890 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0235 hb34 2490701444 le_rfl (by norm_num)).2
  have hb36 : (2752749307940709987163 : Real) / 2 ^ 40 <= Chebyshev.theta (2503691910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0236 hb35 2497192890 le_rfl (by norm_num)).2
  have hb37 : (2759884677346352533108 : Real) / 2 ^ 40 <= Chebyshev.theta (2510170278 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0237 hb36 2503691910 le_rfl (by norm_num)).2
  have hb38 : (2767020898514560722480 : Real) / 2 ^ 40 <= Chebyshev.theta (2516657888 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0238 hb37 2510170278 le_rfl (by norm_num)).2
  have hb39 : (2774157969561981797001 : Real) / 2 ^ 40 <= Chebyshev.theta (2523147270 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0239 hb38 2516657888 le_rfl (by norm_num)).2
  have hb40 : (2781295888961764073759 : Real) / 2 ^ 40 <= Chebyshev.theta (2529637304 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0240 hb39 2523147270 le_rfl (by norm_num)).2
  have hb41 : (2788434653789519556126 : Real) / 2 ^ 40 <= Chebyshev.theta (2536125210 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0241 hb40 2529637304 le_rfl (by norm_num)).2
  have hb42 : (2795574262015462110921 : Real) / 2 ^ 40 <= Chebyshev.theta (2542610574 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0242 hb41 2536125210 le_rfl (by norm_num)).2
  have hb43 : (2802714712578647514897 : Real) / 2 ^ 40 <= Chebyshev.theta (2549109842 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0243 hb42 2542610574 le_rfl (by norm_num)).2
  have hb44 : (2809856002579992649427 : Real) / 2 ^ 40 <= Chebyshev.theta (2555602808 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0244 hb43 2549109842 le_rfl (by norm_num)).2
  have hb45 : (2816998130117724293571 : Real) / 2 ^ 40 <= Chebyshev.theta (2562091374 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0245 hb44 2555602808 le_rfl (by norm_num)).2
  have hb46 : (2824141093178988254574 : Real) / 2 ^ 40 <= Chebyshev.theta (2568584220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0246 hb45 2562091374 le_rfl (by norm_num)).2
  have hb47 : (2831284889407081703316 : Real) / 2 ^ 40 <= Chebyshev.theta (2575075380 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0247 hb46 2568584220 le_rfl (by norm_num)).2
  have hb48 : (2838429517139139237630 : Real) / 2 ^ 40 <= Chebyshev.theta (2581574058 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0248 hb47 2575075380 le_rfl (by norm_num)).2
  have hb49 : (2845574974736297876394 : Real) / 2 ^ 40 <= Chebyshev.theta (2588072142 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0249 hb48 2581574058 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0250 hb49 2588072142 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 2432341758 with hc25 | hc25
  · rcases Nat.lt_or_ge n 2348153220 with hc12 | hc12
    · rcases Nat.lt_or_ge n 2309338502 with hc6 | hc6
      · rcases Nat.lt_or_ge n 2289947064 with hc3 | hc3
        · rcases Nat.lt_or_ge n 2277016902 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0201 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2283491082 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0202 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0203 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2296403384 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0204 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2302871742 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0205 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0206 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2328740634 with hc9 | hc9
        · rcases Nat.lt_or_ge n 2315797218 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0207 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2322269708 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0208 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0209 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2335211688 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0210 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2341677698 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0211 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0212 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2386991442 with hc18 | hc18
      · rcases Nat.lt_or_ge n 2367571980 with hc15 | hc15
        · rcases Nat.lt_or_ge n 2354623410 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0213 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2361102092 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0214 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0215 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2374041764 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0216 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2380519398 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0217 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0218 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2406429924 with hc21 | hc21
        · rcases Nat.lt_or_ge n 2393464394 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0219 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2399943864 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0220 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0221 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2419384532 with hc23 | hc23
          · rcases Nat.lt_or_ge n 2412906648 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0222 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0223 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2425860990 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0224 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0225 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 2510170278 with hc37 | hc37
    · rcases Nat.lt_or_ge n 2471245500 with hc31 | hc31
      · rcases Nat.lt_or_ge n 2451791540 with hc28 | hc28
        · rcases Nat.lt_or_ge n 2438824338 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0226 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2445300450 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0227 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0228 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2458270044 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0229 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2464764374 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0230 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0231 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2490701444 with hc34 | hc34
        · rcases Nat.lt_or_ge n 2477724678 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0232 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2484206694 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0233 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0234 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2497192890 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0235 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2503691910 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0236 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0237 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2549109842 with hc43 | hc43
      · rcases Nat.lt_or_ge n 2529637304 with hc40 | hc40
        · rcases Nat.lt_or_ge n 2516657888 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0238 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2523147270 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0239 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0240 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2536125210 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0241 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2542610574 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0242 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0243 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2568584220 with hc46 | hc46
        · rcases Nat.lt_or_ge n 2555602808 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0244 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2562091374 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0245 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0246 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2581574058 with hc48 | hc48
          · rcases Nat.lt_or_ge n 2575075380 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0247 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0248 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2588072142 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0249 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0250 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (2496462384131083673405 : Real) / 2 ^ 40 <= Chebyshev.theta (2270572190 : Real))
    (n : Nat) (h1 : 2270572190 <= n) (h2 : n <= 2594569591) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2852721260005778301656 : Real) / 2 ^ 40 <= Chebyshev.theta (2594569592 : Real)) :=
  TFPLink.blk hbase n h1 h2
