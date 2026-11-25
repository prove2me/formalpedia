-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.Base.N.ode_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:54.806803+00:00
-- url     : https://prove2.me/submissions/d8d3ec7d-56ae-47f2-8b60-28b3a3354dce

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_LaplaceFoundations_OneParameterSubgroups_OneParam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Filter Topology
open scoped InnerProductSpace
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap ReciprocityTheory.ChartRestriction.DS.Lap.Base ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
theorem _root_.solution (U U' : ℝ → ℂ) (a b : ℂ) (ha : a.re = 0) {δ : ℝ} (hU0 : U 0 = 1)
    (hder : ∀ s ∈ Set.Icc (0 : ℝ) 1, HasDerivAt U (U' s) s)
    (hb : ∀ s ∈ Set.Icc (0 : ℝ) 1, ‖U' s - (a + s * b) * U s‖ ≤ δ) :
    ‖U 1 * cexp (-a) - cexp (b / 2)‖ ≤ δ * Real.exp ‖b‖ := by
  have hδ : 0 ≤ δ := (norm_nonneg _).trans (hb 0 ⟨le_rfl, zero_le_one⟩)
  have hofs : ∀ t : ℝ, HasDerivAt (fun y : ℝ => (y : ℂ)) 1 t := fun t => (hasDerivAt_id t).ofReal_comp
  set g : ℝ → ℂ := fun t => -(a * (t : ℂ)) - (t : ℂ) ^ 2 * b / 2 with hg_def
  have hg : ∀ t : ℝ, HasDerivAt g (-(a + (t : ℂ) * b)) t := by
    intro t
    have h3 := ((hofs t).const_mul a).neg.sub (((hofs t).pow 2).mul_const b |>.div_const 2)
    exact h3.congr_deriv (by first | ring | (norm_num; ring) | norm_num | (simp; ring) | simp)
  set W : ℝ → ℂ := fun t => U t * cexp (g t) with hW
  have hWd : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HasDerivAt W ((U' t - (a + (t : ℂ) * b) * U t) * cexp (g t)) t := by
    intro t ht
    have := (hder t ht).mul (hg t).cexp
    exact this.congr_deriv (by ring)
  have hgre : ∀ t ∈ Set.Icc (0 : ℝ) 1, (g t).re ≤ ‖b‖ / 2 := by
    intro t ht
    have hre : (g t).re = -(t ^ 2 * b.re / 2) := by
      simp only [hg_def]
      simp [Complex.mul_re, ha]
      rw [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    have hb1 : -b.re ≤ ‖b‖ := (neg_le_abs b.re).trans (Complex.abs_re_le_norm b)
    have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
    nlinarith [mul_le_mul_of_nonneg_left hb1 (sq_nonneg t), norm_nonneg b]
  have hmvt := norm_image_sub_le_of_norm_deriv_le_segment' (f := W)
    (C := δ * Real.exp (‖b‖ / 2)) (fun t ht => (hWd t ht).hasDerivWithinAt)
    (fun t ht => by
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := Set.Ico_subset_Icc_self ht
      rw [norm_mul, Complex.norm_exp]
      exact mul_le_mul (hb t ht') (Real.exp_le_exp.mpr (hgre t ht')) (Real.exp_pos _).le hδ)
    1 ⟨zero_le_one, le_rfl⟩
  have hW0 : W 0 = 1 := by simp [hW, hg_def, hU0]
  have hg1 : g 1 + b / 2 = -a := by simp only [hg_def]; push_cast; ring
  have hid : U 1 * cexp (-a) - cexp (b / 2) = (W 1 - W 0) * cexp (b / 2) := by
    rw [hW0, ← hg1]
    simp only [hW, Complex.exp_add]
    ring
  have hre2 : (b / 2).re ≤ ‖b‖ / 2 := by
    have : (b / 2).re = b.re / 2 := by simp
    rw [this]
    linarith [Complex.re_le_norm b]
  rw [hid, norm_mul, Complex.norm_exp]
  calc ‖W 1 - W 0‖ * Real.exp (b / 2).re
      ≤ (δ * Real.exp (‖b‖ / 2) * (1 - 0)) * Real.exp (‖b‖ / 2) :=
        mul_le_mul hmvt (Real.exp_le_exp.mpr hre2) (Real.exp_pos _).le
          (mul_nonneg (mul_nonneg hδ (Real.exp_pos _).le) (by norm_num))
    _ = δ * Real.exp ‖b‖ := by rw [sub_zero, mul_one, mul_assoc, ← Real.exp_add, add_halves]
end ReciprocityTheory.ChartRestriction.DS.Lap.Base.N
