-- Prove2me | solution 1 for ReciprocityTheory.AnForm.integral_Ioi_fsDens_radial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:08:49.057821+00:00
-- url     : https://prove2.me/submissions/5520060b-03fe-4ca4-a465-822bf21b715a

import Definitions.Def_ReciprocityTheory_AnalyticForms_MaIntEmpty
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegralIoiFsDensRadial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm
open MeasureTheory Filter Topology Set
noncomputable section
namespace ReciprocityTheory.AnForm
theorem _root_.solution :
    ∫ r in Ioi (0 : ℝ), r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)) = 1 / (2 * Real.pi) := by
  have hπ := Real.pi_pos
  have key := integral_Ioi_of_hasDerivAt_of_nonneg (a := 0) (l := 0)
    (g := fun r : ℝ => -(2 * Real.pi * (1 + r ^ 2))⁻¹)
    (g' := fun r : ℝ => r * (1 / (Real.pi * (1 + r ^ 2) ^ 2)))
    (by fun_prop (disch := positivity)) ?_ ?_ ?_
  · rw [key]; simp
  · intro r _
    have h1 : (2 * Real.pi * (1 + r ^ 2)) ≠ 0 := by positivity
    have := ((((hasDerivAt_id' r).pow 2).const_add 1).const_mul (2 * Real.pi)).inv h1 |>.neg
    refine this.congr_deriv ?_
    try simp only [Pi.mul_apply, Pi.pow_apply]
    field_simp
    all_goals ring
  · intro r hr
    have : (0 : ℝ) < r := hr
    positivity
  · have h1 : Tendsto (fun r : ℝ => 2 * Real.pi * (1 + r ^ 2)) atTop atTop := by
      apply Tendsto.const_mul_atTop (by positivity)
      exact tendsto_atTop_add_const_left _ _ (tendsto_pow_atTop two_ne_zero)
    simpa using (tendsto_inv_atTop_zero.comp h1).neg
end ReciprocityTheory.AnForm
