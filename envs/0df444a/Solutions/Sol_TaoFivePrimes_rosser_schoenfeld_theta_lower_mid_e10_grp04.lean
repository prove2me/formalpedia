-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp04
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:29:16.839074+00:00
-- url     : https://prove2.me/submissions/6a6114f1-1ba4-43ca-bfe1-dd8920364689

import Mathlib.NumberTheory.Chebyshev
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0151
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0152
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0153
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0154
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0155
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0156
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0157
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0158
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0159
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0160
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0161
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0162
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0163
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0164
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0165
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0166
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0167
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0168
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0169
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0170
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0171
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0172
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0173
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0174
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0175
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0176
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0177
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0178
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0179
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0180
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0181
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0182
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0183
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0184
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0185
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0186
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0187
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0188
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0189
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0190
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0191
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0192
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0193
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0194
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0195
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0196
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0197
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0198
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0199
import Theorems.Thm_TaoFivePrimes_rosser_schoenfeld_theta_lower_mid_e10_seg0200

/-! Link reduction: `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_grp04` (the range 1948709900 <= n <= 2270572189 with its carry in and carry out) from the 50 integer certificate segments `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0151` .. `TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0200`, chained through their carries (segment k's second conjunct is segment k+1's hypothesis), with a balanced case split on n selecting the segment. -/

namespace TFPLink

set_option maxHeartbeats 4000000 in
theorem blk
    (hbase : (2142555716222639034474 : Real) / 2 ^ 40 <= Chebyshev.theta (1948709900 : Real))
    (n : Nat) (h1 : 1948709900 <= n) (h2 : n <= 2270572189) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2496462384131083673405 : Real) / 2 ^ 40 <= Chebyshev.theta (2270572190 : Real)) := by
  have hb0 := hbase
  have hb1 : (2149608580003513663137 : Real) / 2 ^ 40 <= Chebyshev.theta (1955120508 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0151 hb0 1948709900 le_rfl (by norm_num)).2
  have hb2 : (2156662525429490265657 : Real) / 2 ^ 40 <= Chebyshev.theta (1961538290 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0152 hb1 1955120508 le_rfl (by norm_num)).2
  have hb3 : (2163717549813786207224 : Real) / 2 ^ 40 <= Chebyshev.theta (1967959080 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0153 hb2 1961538290 le_rfl (by norm_num)).2
  have hb4 : (2170773649291453503748 : Real) / 2 ^ 40 <= Chebyshev.theta (1974369708 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0154 hb3 1967959080 le_rfl (by norm_num)).2
  have hb5 : (2177830819571454681269 : Real) / 2 ^ 40 <= Chebyshev.theta (1980784754 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0155 hb4 1974369708 le_rfl (by norm_num)).2
  have hb6 : (2184889058071389726732 : Real) / 2 ^ 40 <= Chebyshev.theta (1987204488 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0156 hb5 1980784754 le_rfl (by norm_num)).2
  have hb7 : (2191948361852171486435 : Real) / 2 ^ 40 <= Chebyshev.theta (1993625870 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0157 hb6 1987204488 le_rfl (by norm_num)).2
  have hb8 : (2199008727606675683986 : Real) / 2 ^ 40 <= Chebyshev.theta (2000052114 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0158 hb7 1993625870 le_rfl (by norm_num)).2
  have hb9 : (2206070151261933352904 : Real) / 2 ^ 40 <= Chebyshev.theta (2006458748 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0159 hb8 2000052114 le_rfl (by norm_num)).2
  have hb10 : (2213132629531287397533 : Real) / 2 ^ 40 <= Chebyshev.theta (2012884898 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0160 hb9 2006458748 le_rfl (by norm_num)).2
  have hb11 : (2220196158803955005469 : Real) / 2 ^ 40 <= Chebyshev.theta (2019299834 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0161 hb10 2012884898 le_rfl (by norm_num)).2
  have hb12 : (2227260737350831535071 : Real) / 2 ^ 40 <= Chebyshev.theta (2025730670 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0162 hb11 2019299834 le_rfl (by norm_num)).2
  have hb13 : (2234326362452386862353 : Real) / 2 ^ 40 <= Chebyshev.theta (2032162092 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0163 hb12 2025730670 le_rfl (by norm_num)).2
  have hb14 : (2241393030116404352101 : Real) / 2 ^ 40 <= Chebyshev.theta (2038588568 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0164 hb13 2032162092 le_rfl (by norm_num)).2
  have hb15 : (2248460737752669249524 : Real) / 2 ^ 40 <= Chebyshev.theta (2045016930 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0165 hb14 2038588568 le_rfl (by norm_num)).2
  have hb16 : (2255529481338264148306 : Real) / 2 ^ 40 <= Chebyshev.theta (2051440230 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0166 hb15 2045016930 le_rfl (by norm_num)).2
  have hb17 : (2262599258084256575235 : Real) / 2 ^ 40 <= Chebyshev.theta (2057877008 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0167 hb16 2051440230 le_rfl (by norm_num)).2
  have hb18 : (2269670066390112996750 : Real) / 2 ^ 40 <= Chebyshev.theta (2064310178 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0168 hb17 2057877008 le_rfl (by norm_num)).2
  have hb19 : (2276741901776870006678 : Real) / 2 ^ 40 <= Chebyshev.theta (2070743618 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0169 hb18 2064310178 le_rfl (by norm_num)).2
  have hb20 : (2283814761670500529538 : Real) / 2 ^ 40 <= Chebyshev.theta (2077179720 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0170 hb19 2070743618 le_rfl (by norm_num)).2
  have hb21 : (2290888642582652706783 : Real) / 2 ^ 40 <= Chebyshev.theta (2083607550 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0171 hb20 2077179720 le_rfl (by norm_num)).2
  have hb22 : (2297963541548748441431 : Real) / 2 ^ 40 <= Chebyshev.theta (2090045220 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0172 hb21 2083607550 le_rfl (by norm_num)).2
  have hb23 : (2305039455255709368148 : Real) / 2 ^ 40 <= Chebyshev.theta (2096476622 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0173 hb22 2090045220 le_rfl (by norm_num)).2
  have hb24 : (2312116380986610276859 : Real) / 2 ^ 40 <= Chebyshev.theta (2102911358 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0174 hb23 2096476622 le_rfl (by norm_num)).2
  have hb25 : (2319194315168253541602 : Real) / 2 ^ 40 <= Chebyshev.theta (2109347432 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0175 hb24 2102911358 le_rfl (by norm_num)).2
  have hb26 : (2326273254555474624032 : Real) / 2 ^ 40 <= Chebyshev.theta (2115776504 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0176 hb25 2109347432 le_rfl (by norm_num)).2
  have hb27 : (2333353197015221160890 : Real) / 2 ^ 40 <= Chebyshev.theta (2122216332 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0177 hb26 2115776504 le_rfl (by norm_num)).2
  have hb28 : (2340434140871044984611 : Real) / 2 ^ 40 <= Chebyshev.theta (2128664342 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0178 hb27 2122216332 le_rfl (by norm_num)).2
  have hb29 : (2347516083761033438251 : Real) / 2 ^ 40 <= Chebyshev.theta (2135117910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0179 hb28 2128664342 le_rfl (by norm_num)).2
  have hb30 : (2354599022638181506045 : Real) / 2 ^ 40 <= Chebyshev.theta (2141560592 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0180 hb29 2135117910 le_rfl (by norm_num)).2
  have hb31 : (2361682952397416116576 : Real) / 2 ^ 40 <= Chebyshev.theta (2147996454 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0181 hb30 2141560592 le_rfl (by norm_num)).2
  have hb32 : (2368767870586396887102 : Real) / 2 ^ 40 <= Chebyshev.theta (2154439202 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0182 hb31 2147996454 le_rfl (by norm_num)).2
  have hb33 : (2375853774907961877917 : Real) / 2 ^ 40 <= Chebyshev.theta (2160883494 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0183 hb32 2154439202 le_rfl (by norm_num)).2
  have hb34 : (2382940662433257525687 : Real) / 2 ^ 40 <= Chebyshev.theta (2167331012 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0184 hb33 2160883494 le_rfl (by norm_num)).2
  have hb35 : (2390028530630121442800 : Real) / 2 ^ 40 <= Chebyshev.theta (2173778490 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0185 hb34 2167331012 le_rfl (by norm_num)).2
  have hb36 : (2397117376115514718861 : Real) / 2 ^ 40 <= Chebyshev.theta (2180219600 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0186 hb35 2173778490 le_rfl (by norm_num)).2
  have hb37 : (2404207197326489006750 : Real) / 2 ^ 40 <= Chebyshev.theta (2186676132 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0187 hb36 2180219600 le_rfl (by norm_num)).2
  have hb38 : (2411297990909031579662 : Real) / 2 ^ 40 <= Chebyshev.theta (2193121818 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0188 hb37 2186676132 le_rfl (by norm_num)).2
  have hb39 : (2418389753752875226829 : Real) / 2 ^ 40 <= Chebyshev.theta (2199570648 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0189 hb38 2193121818 le_rfl (by norm_num)).2
  have hb40 : (2425482484528397461524 : Real) / 2 ^ 40 <= Chebyshev.theta (2206033910 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0190 hb39 2199570648 le_rfl (by norm_num)).2
  have hb41 : (2432576179717289915214 : Real) / 2 ^ 40 <= Chebyshev.theta (2212483812 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0191 hb40 2206033910 le_rfl (by norm_num)).2
  have hb42 : (2439670836597045419440 : Real) / 2 ^ 40 <= Chebyshev.theta (2218937742 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0192 hb41 2212483812 le_rfl (by norm_num)).2
  have hb43 : (2446766452286257057121 : Real) / 2 ^ 40 <= Chebyshev.theta (2225391660 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0193 hb42 2218937742 le_rfl (by norm_num)).2
  have hb44 : (2453863024273229621381 : Real) / 2 ^ 40 <= Chebyshev.theta (2231843310 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0194 hb43 2225391660 le_rfl (by norm_num)).2
  have hb45 : (2460960549759169179200 : Real) / 2 ^ 40 <= Chebyshev.theta (2238299342 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0195 hb44 2231843310 le_rfl (by norm_num)).2
  have hb46 : (2468059026090412715505 : Real) / 2 ^ 40 <= Chebyshev.theta (2244757070 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0196 hb45 2238299342 le_rfl (by norm_num)).2
  have hb47 : (2475158450194278205972 : Real) / 2 ^ 40 <= Chebyshev.theta (2251204400 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0197 hb46 2244757070 le_rfl (by norm_num)).2
  have hb48 : (2482258819514414776663 : Real) / 2 ^ 40 <= Chebyshev.theta (2257666614 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0198 hb47 2251204400 le_rfl (by norm_num)).2
  have hb49 : (2489360132107556649327 : Real) / 2 ^ 40 <= Chebyshev.theta (2264117898 : Real) :=
    (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0199 hb48 2257666614 le_rfl (by norm_num)).2
  refine ⟨?_, (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0200 hb49 2264117898 le_rfl (by norm_num)).2⟩
  rcases Nat.lt_or_ge n 2109347432 with hc25 | hc25
  · rcases Nat.lt_or_ge n 2025730670 with hc12 | hc12
    · rcases Nat.lt_or_ge n 1987204488 with hc6 | hc6
      · rcases Nat.lt_or_ge n 1967959080 with hc3 | hc3
        · rcases Nat.lt_or_ge n 1955120508 with hc1 | hc1
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0151 hb0 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1961538290 with hc2 | hc2
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0152 hb1 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0153 hb2 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 1974369708 with hc4 | hc4
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0154 hb3 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 1980784754 with hc5 | hc5
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0155 hb4 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0156 hb5 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2006458748 with hc9 | hc9
        · rcases Nat.lt_or_ge n 1993625870 with hc7 | hc7
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0157 hb6 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2000052114 with hc8 | hc8
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0158 hb7 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0159 hb8 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2012884898 with hc10 | hc10
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0160 hb9 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2019299834 with hc11 | hc11
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0161 hb10 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0162 hb11 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2064310178 with hc18 | hc18
      · rcases Nat.lt_or_ge n 2045016930 with hc15 | hc15
        · rcases Nat.lt_or_ge n 2032162092 with hc13 | hc13
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0163 hb12 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2038588568 with hc14 | hc14
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0164 hb13 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0165 hb14 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2051440230 with hc16 | hc16
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0166 hb15 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2057877008 with hc17 | hc17
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0167 hb16 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0168 hb17 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2083607550 with hc21 | hc21
        · rcases Nat.lt_or_ge n 2070743618 with hc19 | hc19
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0169 hb18 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2077179720 with hc20 | hc20
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0170 hb19 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0171 hb20 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2096476622 with hc23 | hc23
          · rcases Nat.lt_or_ge n 2090045220 with hc22 | hc22
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0172 hb21 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0173 hb22 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2102911358 with hc24 | hc24
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0174 hb23 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0175 hb24 n (by omega) (by omega)).1
  · rcases Nat.lt_or_ge n 2186676132 with hc37 | hc37
    · rcases Nat.lt_or_ge n 2147996454 with hc31 | hc31
      · rcases Nat.lt_or_ge n 2128664342 with hc28 | hc28
        · rcases Nat.lt_or_ge n 2115776504 with hc26 | hc26
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0176 hb25 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2122216332 with hc27 | hc27
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0177 hb26 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0178 hb27 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2135117910 with hc29 | hc29
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0179 hb28 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2141560592 with hc30 | hc30
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0180 hb29 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0181 hb30 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2167331012 with hc34 | hc34
        · rcases Nat.lt_or_ge n 2154439202 with hc32 | hc32
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0182 hb31 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2160883494 with hc33 | hc33
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0183 hb32 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0184 hb33 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2173778490 with hc35 | hc35
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0185 hb34 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2180219600 with hc36 | hc36
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0186 hb35 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0187 hb36 n (by omega) (by omega)).1
    · rcases Nat.lt_or_ge n 2225391660 with hc43 | hc43
      · rcases Nat.lt_or_ge n 2206033910 with hc40 | hc40
        · rcases Nat.lt_or_ge n 2193121818 with hc38 | hc38
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0188 hb37 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2199570648 with hc39 | hc39
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0189 hb38 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0190 hb39 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2212483812 with hc41 | hc41
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0191 hb40 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2218937742 with hc42 | hc42
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0192 hb41 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0193 hb42 n (by omega) (by omega)).1
      · rcases Nat.lt_or_ge n 2244757070 with hc46 | hc46
        · rcases Nat.lt_or_ge n 2231843310 with hc44 | hc44
          · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0194 hb43 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2238299342 with hc45 | hc45
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0195 hb44 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0196 hb45 n (by omega) (by omega)).1
        · rcases Nat.lt_or_ge n 2257666614 with hc48 | hc48
          · rcases Nat.lt_or_ge n 2251204400 with hc47 | hc47
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0197 hb46 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0198 hb47 n (by omega) (by omega)).1
          · rcases Nat.lt_or_ge n 2264117898 with hc49 | hc49
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0199 hb48 n (by omega) (by omega)).1
            · exact (TaoFivePrimes.rosser_schoenfeld_theta_lower_mid_e10_seg0200 hb49 n (by omega) (by omega)).1

end TFPLink

theorem solution
    (hbase : (2142555716222639034474 : Real) / 2 ^ 40 <= Chebyshev.theta (1948709900 : Real))
    (n : Nat) (h1 : 1948709900 <= n) (h2 : n <= 2270572189) :
    (((n : Real) + 1) - 10 * Real.sqrt ((n : Real) + 1) <= Chebyshev.theta (n : Real)) /\
      ((2496462384131083673405 : Real) / 2 ^ 40 <= Chebyshev.theta (2270572190 : Real)) :=
  TFPLink.blk hbase n h1 h2
