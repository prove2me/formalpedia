-- Prove2me | solution 1 for TaoFivePrimes.rosser_schoenfeld_theta_lower_finite
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-17T14:26:57.42719+00:00
-- url     : https://prove2.me/submissions/c2641f48-dda7-4604-be55-d5c78c9d3f59

import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Definitions.Def_TaoFivePrimes_theta_cert_tables
import Theorems.Thm_TaoFivePrimes_theta_cert_plist_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_primesLE_eq
import Theorems.Thm_TaoFivePrimes_theta_cert_clbZ_le_log
import Theorems.Thm_TaoFivePrimes_theta_cert_blocks_1
import Theorems.Thm_TaoFivePrimes_theta_cert_blocks_2
import Theorems.Thm_TaoFivePrimes_theta_cert_blocks_3
import Theorems.Thm_TaoFivePrimes_theta_cert_blocks_4
set_option maxRecDepth 1000000
set_option maxHeartbeats 4000000

namespace TaoFivePrimes

open Finset

lemma cover (n : ℕ) (h1 : 255 ≤ n) (h2 : n ≤ 1420) :
    ∃ bl, bl ∈ blocks ∧ bl.1 ≤ n ∧ n ≤ bl.2 := by
  by_cases hb0 : n ≤ 263
  · exact ⟨(255, 263), by decide, by omega, hb0⟩
  by_cases hb1 : n ≤ 275
  · exact ⟨(264, 275), by decide, by omega, hb1⟩
  by_cases hb2 : n ≤ 286
  · exact ⟨(276, 286), by decide, by omega, hb2⟩
  by_cases hb3 : n ≤ 304
  · exact ⟨(287, 304), by decide, by omega, hb3⟩
  by_cases hb4 : n ≤ 311
  · exact ⟨(305, 311), by decide, by omega, hb4⟩
  by_cases hb5 : n ≤ 323
  · exact ⟨(312, 323), by decide, by omega, hb5⟩
  by_cases hb6 : n ≤ 334
  · exact ⟨(324, 334), by decide, by omega, hb6⟩
  by_cases hb7 : n ≤ 340
  · exact ⟨(335, 340), by decide, by omega, hb7⟩
  by_cases hb8 : n ≤ 347
  · exact ⟨(341, 347), by decide, by omega, hb8⟩
  by_cases hb9 : n ≤ 353
  · exact ⟨(348, 353), by decide, by omega, hb9⟩
  by_cases hb10 : n ≤ 366
  · exact ⟨(354, 366), by decide, by omega, hb10⟩
  by_cases hb11 : n ≤ 377
  · exact ⟨(367, 377), by decide, by omega, hb11⟩
  by_cases hb12 : n ≤ 384
  · exact ⟨(378, 384), by decide, by omega, hb12⟩
  by_cases hb13 : n ≤ 396
  · exact ⟨(385, 396), by decide, by omega, hb13⟩
  by_cases hb14 : n ≤ 409
  · exact ⟨(397, 409), by decide, by omega, hb14⟩
  by_cases hb15 : n ≤ 422
  · exact ⟨(410, 422), by decide, by omega, hb15⟩
  by_cases hb16 : n ≤ 434
  · exact ⟨(423, 434), by decide, by omega, hb16⟩
  by_cases hb17 : n ≤ 447
  · exact ⟨(435, 447), by decide, by omega, hb17⟩
  by_cases hb18 : n ≤ 460
  · exact ⟨(448, 460), by decide, by omega, hb18⟩
  by_cases hb19 : n ≤ 479
  · exact ⟨(461, 479), by decide, by omega, hb19⟩
  by_cases hb20 : n ≤ 498
  · exact ⟨(480, 498), by decide, by omega, hb20⟩
  by_cases hb21 : n ≤ 518
  · exact ⟨(499, 518), by decide, by omega, hb21⟩
  by_cases hb22 : n ≤ 532
  · exact ⟨(519, 532), by decide, by omega, hb22⟩
  by_cases hb23 : n ≤ 544
  · exact ⟨(533, 544), by decide, by omega, hb23⟩
  by_cases hb24 : n ≤ 550
  · exact ⟨(545, 550), by decide, by omega, hb24⟩
  by_cases hb25 : n ≤ 558
  · exact ⟨(551, 558), by decide, by omega, hb25⟩
  by_cases hb26 : n ≤ 564
  · exact ⟨(559, 564), by decide, by omega, hb26⟩
  by_cases hb27 : n ≤ 570
  · exact ⟨(565, 570), by decide, by omega, hb27⟩
  by_cases hb28 : n ≤ 584
  · exact ⟨(571, 584), by decide, by omega, hb28⟩
  by_cases hb29 : n ≤ 590
  · exact ⟨(585, 590), by decide, by omega, hb29⟩
  by_cases hb30 : n ≤ 597
  · exact ⟨(591, 597), by decide, by omega, hb30⟩
  by_cases hb31 : n ≤ 604
  · exact ⟨(598, 604), by decide, by omega, hb31⟩
  by_cases hb32 : n ≤ 617
  · exact ⟨(605, 617), by decide, by omega, hb32⟩
  by_cases hb33 : n ≤ 637
  · exact ⟨(618, 637), by decide, by omega, hb33⟩
  by_cases hb34 : n ≤ 651
  · exact ⟨(638, 651), by decide, by omega, hb34⟩
  by_cases hb35 : n ≤ 670
  · exact ⟨(652, 670), by decide, by omega, hb35⟩
  by_cases hb36 : n ≤ 691
  · exact ⟨(671, 691), by decide, by omega, hb36⟩
  by_cases hb37 : n ≤ 718
  · exact ⟨(692, 718), by decide, by omega, hb37⟩
  by_cases hb38 : n ≤ 739
  · exact ⟨(719, 739), by decide, by omega, hb38⟩
  by_cases hb39 : n ≤ 759
  · exact ⟨(740, 759), by decide, by omega, hb39⟩
  by_cases hb40 : n ≤ 779
  · exact ⟨(760, 779), by decide, by omega, hb40⟩
  by_cases hb41 : n ≤ 800
  · exact ⟨(780, 800), by decide, by omega, hb41⟩
  by_cases hb42 : n ≤ 815
  · exact ⟨(801, 815), by decide, by omega, hb42⟩
  by_cases hb43 : n ≤ 828
  · exact ⟨(816, 828), by decide, by omega, hb43⟩
  by_cases hb44 : n ≤ 856
  · exact ⟨(829, 856), by decide, by omega, hb44⟩
  by_cases hb45 : n ≤ 877
  · exact ⟨(857, 877), by decide, by omega, hb45⟩
  by_cases hb46 : n ≤ 897
  · exact ⟨(878, 897), by decide, by omega, hb46⟩
  by_cases hb47 : n ≤ 919
  · exact ⟨(898, 919), by decide, by omega, hb47⟩
  by_cases hb48 : n ≤ 940
  · exact ⟨(920, 940), by decide, by omega, hb48⟩
  by_cases hb49 : n ≤ 962
  · exact ⟨(941, 962), by decide, by omega, hb49⟩
  by_cases hb50 : n ≤ 975
  · exact ⟨(963, 975), by decide, by omega, hb50⟩
  by_cases hb51 : n ≤ 989
  · exact ⟨(976, 989), by decide, by omega, hb51⟩
  by_cases hb52 : n ≤ 1004
  · exact ⟨(990, 1004), by decide, by omega, hb52⟩
  by_cases hb53 : n ≤ 1018
  · exact ⟨(1005, 1018), by decide, by omega, hb53⟩
  by_cases hb54 : n ≤ 1040
  · exact ⟨(1019, 1040), by decide, by omega, hb54⟩
  by_cases hb55 : n ≤ 1068
  · exact ⟨(1041, 1068), by decide, by omega, hb55⟩
  by_cases hb56 : n ≤ 1104
  · exact ⟨(1069, 1104), by decide, by omega, hb56⟩
  by_cases hb57 : n ≤ 1140
  · exact ⟨(1105, 1140), by decide, by omega, hb57⟩
  by_cases hb58 : n ≤ 1169
  · exact ⟨(1141, 1169), by decide, by omega, hb58⟩
  by_cases hb59 : n ≤ 1191
  · exact ⟨(1170, 1191), by decide, by omega, hb59⟩
  by_cases hb60 : n ≤ 1213
  · exact ⟨(1192, 1213), by decide, by omega, hb60⟩
  by_cases hb61 : n ≤ 1235
  · exact ⟨(1214, 1235), by decide, by omega, hb61⟩
  by_cases hb62 : n ≤ 1264
  · exact ⟨(1236, 1264), by decide, by omega, hb62⟩
  by_cases hb63 : n ≤ 1286
  · exact ⟨(1265, 1286), by decide, by omega, hb63⟩
  by_cases hb64 : n ≤ 1308
  · exact ⟨(1287, 1308), by decide, by omega, hb64⟩
  by_cases hb65 : n ≤ 1352
  · exact ⟨(1309, 1352), by decide, by omega, hb65⟩
  by_cases hb66 : n ≤ 1375
  · exact ⟨(1353, 1375), by decide, by omega, hb66⟩
  by_cases hb67 : n ≤ 1396
  · exact ⟨(1376, 1396), by decide, by omega, hb67⟩
  by_cases hb68 : n ≤ 1404
  · exact ⟨(1397, 1404), by decide, by omega, hb68⟩
  by_cases hb69 : n ≤ 1412
  · exact ⟨(1405, 1412), by decide, by omega, hb69⟩
  exact ⟨(1413, 1420), by decide, by omega, h2⟩

/-- `x - 2*sqrt x` is monotone on `x >= 1`. -/
lemma mono_f (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) :
    x - 2 * Real.sqrt x ≤ y - 2 * Real.sqrt y := by
  have hsx : 1 ≤ Real.sqrt x := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_le_sqrt hx
  have hsy : Real.sqrt x ≤ Real.sqrt y := Real.sqrt_le_sqrt hxy
  have hsq : (Real.sqrt x - 1) ^ 2 ≤ (Real.sqrt y - 1) ^ 2 := by
    apply sq_le_sq'
    · linarith
    · linarith
  have e1 : x - 2 * Real.sqrt x = (Real.sqrt x - 1) ^ 2 - 1 := by
    rw [sub_sq, Real.sq_sqrt (by linarith), one_pow]
    ring
  have e2 : y - 2 * Real.sqrt y = (Real.sqrt y - 1) ^ 2 - 1 := by
    rw [sub_sq, Real.sq_sqrt (by linarith), one_pow]
    ring
  rw [e1, e2]
  linarith

lemma theta_lower_int (n : ℕ) (hn1 : 255 ≤ n) (hn2 : n ≤ 1420) :
    ((min (n + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (n + 1) 1420 : ℕ) : ℝ)
      < Chebyshev.theta (n : ℝ) := by
  obtain ⟨bl, hblmem, hbl1, hbl2⟩ := cover n hn1 hn2
  have hblock : ((min (bl.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (bl.2 + 1) 1420 : ℕ) : ℝ)
      < Chebyshev.theta ((bl.1 : ℕ) : ℝ) := by
    simp only [blocks, List.mem_cons, List.mem_nil_iff, or_false] at hblmem
    rcases hblmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
    all_goals cases h
    all_goals (first | exact theta_cert_blocks_1 _ (by decide) | exact theta_cert_blocks_2 _ (by decide) | exact theta_cert_blocks_3 _ (by decide) | exact theta_cert_blocks_4 _ (by decide))
  have hTmono : ((min (n + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (n + 1) 1420 : ℕ) : ℝ)
      ≤ ((min (bl.2 + 1) 1420 : ℕ) : ℝ) - 2 * Real.sqrt ((min (bl.2 + 1) 1420 : ℕ) : ℝ) := by
    apply mono_f
    · exact_mod_cast (le_min (by omega : 1 ≤ n + 1) (by norm_num : 1 ≤ 1420))
    · rcases le_total (bl.2 + 1) 1420 with hbT | hbT
      · rw [min_eq_left hbT, min_eq_left ((Nat.succ_le_succ hbl2).trans hbT)]
        exact_mod_cast (Nat.succ_le_succ hbl2)
      · rcases le_total (n + 1) 1420 with hnT | hnT
        · rw [min_eq_left hnT, min_eq_right hbT]
          exact_mod_cast hnT
        · rw [min_eq_right hnT, min_eq_right hbT]
  have hthmono : Chebyshev.theta ((bl.1 : ℕ) : ℝ) ≤ Chebyshev.theta (n : ℝ) :=
    Chebyshev.theta_mono (by exact_mod_cast hbl1)
  linarith [hblock, hTmono, hthmono]

/-- Rosser-Schoenfeld (1962), Theorem 19 (finite window): for `255 <= t <= 1420`,
`t - 2*sqrt t < theta t`. -/
theorem solution (t : ℝ) (h1 : 255 ≤ t) (h2 : t ≤ 1420) :
    t - 2 * Real.sqrt t < Chebyshev.theta t := by
  set n := ⌊t⌋₊ with hn
  have hn1 : 255 ≤ n := Nat.le_floor (by exact_mod_cast h1)
  have hn2 : n ≤ 1420 := by
    have h : (n : ℝ) ≤ 1420 := by
      rw [hn]
      exact (Nat.floor_le (by linarith : (0 : ℝ) ≤ t)).trans h2
    exact_mod_cast h
  have hint := theta_lower_int n hn1 hn2
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have htle : t ≤ ((min (n + 1) 1420 : ℕ) : ℝ) := by
    rcases le_total (n + 1) 1420 with hlt | hlt
    · rw [min_eq_left hlt]
      have h := Nat.lt_floor_add_one t
      rw [← hn] at h
      exact_mod_cast h.le
    · rw [min_eq_right hlt]
      exact_mod_cast h2
  have hmono := mono_f t ((min (n + 1) 1420 : ℕ) : ℝ) ht1 htle
  rw [Chebyshev.theta_eq_theta_coe_floor t, ← hn]
  linarith [hint, hmono]

end TaoFivePrimes


open TaoFivePrimes

/-- The verification harness looks for `theorem solution` in the root
namespace, so the namespaced proof above is re-exported at the root. -/
theorem solution (t : ℝ) (h1 : 255 ≤ t) (h2 : t ≤ 1420) :
    t - 2 * Real.sqrt t < Chebyshev.theta t :=
  TaoFivePrimes.solution t h1 h2
