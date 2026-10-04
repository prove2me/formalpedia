-- Prove2me | solution 1 for TaoFivePrimes.eta0_dyadic_integral
-- status  : ACCEPTED   (prove)
-- author  : @Hartmann_Psi
-- created : 2026-09-14T05:20:07.150265+00:00
-- url     : https://prove2.me/submissions/638b8cea-3ab4-4afb-bd53-329590eae93b

import Mathlib
import Definitions.Def_TaoFivePrimes_RepresentationCount

open MeasureTheory Set

section PartE0
open MeasureTheory Set
namespace TaoE0

open TaoFivePrimes

/-- The dyadic window condition, as an interval in `W`. -/
theorem window_iff (x d w W : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) (hW : 0 < W) :
    (x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W)
      ↔ (max (x / (2 * d)) w ≤ W ∧ W ≤ min (x / d) (2 * w)) := by
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hA : x / (2 * d) ≤ W := by
      rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at h1
      linarith
    have hB : W ≤ x / d := by
      rw [le_div_iff₀ hd]
      rw [le_div_iff₀ hW] at h2
      linarith
    exact ⟨max_le hA h4, le_min hB (by linarith)⟩
  · rintro ⟨h1, h2⟩
    have hA : x / (2 * d) ≤ W := le_trans (le_max_left _ _) h1
    have h4 : w ≤ W := le_trans (le_max_right _ _) h1
    have hB : W ≤ x / d := le_trans h2 (min_le_left _ _)
    have hC : W ≤ 2 * w := le_trans h2 (min_le_right _ _)
    refine ⟨?_, ?_, by linarith, h4⟩
    · rw [div_le_iff₀ (by positivity)]
      rw [div_le_iff₀ (by positivity)] at hA
      linarith
    · rw [le_div_iff₀ hW]
      rw [le_div_iff₀ hd] at hB
      linarith

/-- The integral of `1/W` over the dyadic window. -/
theorem window_integral (L U : ℝ) (hL : 0 < L) :
    (∫ W in Set.Ioi (0 : ℝ), Set.indicator (Set.Icc L U) (fun W => 1 / W) W)
      = if L ≤ U then Real.log (U / L) else 0 := by
  classical
  have hmeas : MeasurableSet (Set.Icc L U) := measurableSet_Icc
  have hsub : Set.Icc L U ⊆ Set.Ioi (0 : ℝ) := by
    intro t ht
    exact lt_of_lt_of_le hL ht.1
  rw [MeasureTheory.setIntegral_indicator hmeas]
  rw [Set.inter_eq_self_of_subset_right hsub]
  by_cases h : L ≤ U
  · rw [if_pos h]
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le h]
    exact integral_one_div_of_pos hL (lt_of_lt_of_le hL h)
  · rw [if_neg h]
    rw [Set.Icc_eq_empty h]
    simp

/-- **Tao, Section 1, the identity (eta0)**: the logarithmic cutoff is the dyadic average
of the product of the two window indicators. -/
theorem eta0_integral_rep (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    4 * (∫ W in Set.Ioi (0 : ℝ),
        (if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then (1 : ℝ) / W else 0))
      = eta0 (d * w / x) := by
  classical
  set L : ℝ := max (x / (2 * d)) w with hLdef
  set U : ℝ := min (x / d) (2 * w) with hUdef
  have hL : 0 < L := lt_of_lt_of_le hw (le_max_right _ _)
  have hcongr : ∀ W ∈ Set.Ioi (0 : ℝ),
      (if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then (1 : ℝ) / W else 0)
        = Set.indicator (Set.Icc L U) (fun W => 1 / W) W := by
    intro W hW
    rw [Set.indicator_apply]
    by_cases hc : x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W
    · rw [if_pos hc, if_pos (Set.mem_Icc.mpr ((window_iff x d w W hx hd hw hW).mp hc))]
    · rw [if_neg hc, if_neg ?_]
      intro hmem
      exact hc ((window_iff x d w W hx hd hw hW).mpr (Set.mem_Icc.mp hmem))
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hcongr, window_integral L U hL]
  -- the four regimes
  have ht : 0 < d * w / x := by positivity
  have hkey : x / d = w / (d * w / x) := by field_simp
  by_cases hA : x ≤ 2 * (d * w)
  · -- `L = w` and `U = x / d`
    have hLw : L = w := by
      rw [hLdef, max_eq_right]
      rw [div_le_iff₀ (by positivity)]
      linarith
    have hUx : U = x / d := by
      rw [hUdef, min_eq_left]
      rw [div_le_iff₀ hd]
      linarith
    rw [hLw, hUx]
    by_cases hB : d * w ≤ x
    · -- `1/2 ≤ t ≤ 1`
      have hle : w ≤ x / d := by rw [le_div_iff₀ hd]; linarith
      rw [if_pos hle]
      have hratio : x / d / w = x / (d * w) := by field_simp
      rw [hratio]
      have hteq : Real.log (x / (d * w)) = -Real.log (d * w / x) := by
        rw [← Real.log_inv]
        congr 1
        field_simp
      rw [hteq]
      -- evaluate `eta0`
      unfold eta0
      rw [if_pos ht]
      have h1 : Real.log (2 * (d * w / x)) = Real.log 2 + Real.log (d * w / x) :=
        Real.log_mul (by norm_num) (ne_of_gt ht)
      have hnn : 0 ≤ Real.log (2 * (d * w / x)) := by
        apply Real.log_nonneg
        have heq : 2 * (d * w / x) = (2 * (d * w)) / x := by ring
        rw [heq, le_div_iff₀ hx, one_mul]
        exact hA
      have habs : |Real.log (2 * (d * w / x))| = Real.log 2 + Real.log (d * w / x) := by
        rw [abs_of_nonneg hnn, h1]
      rw [habs]
      have hmax : max 0 (Real.log 2 - (Real.log 2 + Real.log (d * w / x)))
          = -Real.log (d * w / x) := by
        rw [max_eq_right]
        · ring
        · have : Real.log (d * w / x) ≤ 0 := by
            apply Real.log_nonpos ht.le
            rw [div_le_one hx]
            linarith
          linarith
      rw [hmax]
    · -- `t > 1`, both sides vanish
      push_neg at hB
      have hgt : x / d < w := by rw [div_lt_iff₀ hd]; linarith
      rw [if_neg (not_le.mpr hgt)]
      unfold eta0
      rw [if_pos ht]
      have h1 : Real.log 2 ≤ |Real.log (2 * (d * w / x))| := by
        have hge : (1 : ℝ) ≤ d * w / x := by rw [le_div_iff₀ hx]; linarith
        have : Real.log 2 ≤ Real.log (2 * (d * w / x)) := by
          apply Real.log_le_log (by norm_num)
          nlinarith
        exact le_trans this (le_abs_self _)
      rw [max_eq_left (by linarith)]
  · -- `L = x / (2 d)` and `U = 2 w`
    push_neg at hA
    have hLx : L = x / (2 * d) := by
      rw [hLdef, max_eq_left]
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hU2 : U = 2 * w := by
      rw [hUdef, min_eq_right]
      rw [le_div_iff₀ hd]
      linarith
    rw [hLx, hU2]
    by_cases hB : x ≤ 4 * (d * w)
    · -- `1/4 ≤ t ≤ 1/2`
      have hle : x / (2 * d) ≤ 2 * w := by rw [div_le_iff₀ (by positivity)]; linarith
      rw [if_pos hle]
      have hratio : 2 * w / (x / (2 * d)) = 4 * (d * w / x) := by field_simp; ring
      rw [hratio]
      unfold eta0
      rw [if_pos ht]
      have hnp : Real.log (2 * (d * w / x)) ≤ 0 := by
        apply Real.log_nonpos (by positivity)
        have heq : 2 * (d * w / x) = (2 * (d * w)) / x := by ring
        rw [heq, div_le_one hx]
        linarith
      have habs : |Real.log (2 * (d * w / x))| = -Real.log (2 * (d * w / x)) :=
        abs_of_nonpos hnp
      rw [habs]
      have h4 : Real.log (4 * (d * w / x)) = Real.log 2 + Real.log (2 * (d * w / x)) := by
        rw [← Real.log_mul (by norm_num) (by positivity)]
        congr 1
        ring
      have hmax : max 0 (Real.log 2 - -Real.log (2 * (d * w / x)))
          = Real.log (4 * (d * w / x)) := by
        rw [h4, max_eq_right]
        · ring
        · have : 0 ≤ Real.log (4 * (d * w / x)) := by
            apply Real.log_nonneg
            have heq : 4 * (d * w / x) = (4 * (d * w)) / x := by ring
            rw [heq, le_div_iff₀ hx, one_mul]
            exact hB
          rw [h4] at this
          linarith
      rw [hmax]
    · -- `t < 1/4`, both sides vanish
      push_neg at hB
      have hgt : 2 * w < x / (2 * d) := by rw [lt_div_iff₀ (by positivity)]; linarith
      rw [if_neg (not_le.mpr hgt)]
      unfold eta0
      rw [if_pos ht]
      have h1 : Real.log 2 ≤ |Real.log (2 * (d * w / x))| := by
        have hsm : 2 * (d * w / x) ≤ 1 / 2 := by
          have heq : 2 * (d * w / x) = (2 * (d * w)) / x := by ring
          rw [heq, div_le_iff₀ hx]
          linarith
        have : Real.log (2 * (d * w / x)) ≤ Real.log (1 / 2) := by
          apply Real.log_le_log (by positivity) hsm
        have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at this
        calc Real.log 2 = -(-Real.log 2) := by ring
          _ ≤ -Real.log (2 * (d * w / x)) := by linarith
          _ ≤ |Real.log (2 * (d * w / x))| := neg_le_abs _
      rw [max_eq_left (by linarith)]

end TaoE0
end PartE0

theorem solution (x d w : ℝ) (hx : 0 < x) (hd : 0 < d) (hw : 0 < w) :
    4 * (∫ W in Set.Ioi (0 : ℝ),
        (if x / (2 * W) ≤ d ∧ d ≤ x / W ∧ W / 2 ≤ w ∧ w ≤ W then (1 : ℝ) / W else 0))
      = TaoFivePrimes.eta0 (d * w / x) :=
  TaoE0.eta0_integral_rep x d w hx hd hw
