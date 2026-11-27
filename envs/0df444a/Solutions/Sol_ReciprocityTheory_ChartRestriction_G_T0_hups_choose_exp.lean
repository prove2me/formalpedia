-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.hups_choose_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:43:44.132069+00:00
-- url     : https://prove2.me/submissions/119a3209-50ff-42b7-96f3-a669c26e5d6b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormLineSectionPow
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HupsChooseRatio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_choose_ratio
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_hups_pow_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution (n p a : ℕ) (hp : p ≤ n) :
    (((n + a).choose a : ℕ) : ℝ) ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
  have h1 := hups_choose_ratio n p hp a
  have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hcast : (((n - p : ℕ) : ℝ)) = (n : ℝ) - p := by rw [Nat.cast_sub hp]
  have hx : 0 ≤ (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) := by positivity
  have h2 := hups_pow_exp _ hx a
  have e : 1 + (((n - p : ℕ) : ℝ)) / ((p : ℝ) + 1) = ((n : ℝ) + 1) / ((p : ℝ) + 1) := by
    rw [hcast]; field_simp; ring
  rw [e, div_pow] at h2
  have hpa : (0 : ℝ) < ((p : ℝ) + 1) ^ a := by positivity
  have hB : (0 : ℝ) ≤ (((p + a).choose a : ℕ) : ℝ) := by positivity
  have h3 : (((p + a).choose a : ℕ) : ℝ) * ((n : ℝ) + 1) ^ a / ((p : ℝ) + 1) ^ a ≤
      (((p + a).choose a : ℕ) : ℝ) * Real.exp (a * (((n - p : ℕ) : ℝ) / ((p : ℝ) + 1))) := by
    rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left h2 hB
  refine le_trans ?_ h3
  rw [le_div_iff₀ hpa]
  exact h1
end ReciprocityTheory.ChartRestriction.G.T0
