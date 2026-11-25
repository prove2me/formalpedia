-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.integrable_norm_monomial_sq_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:30:37.958535+00:00
-- url     : https://prove2.me/submissions/91e5125d-6e80-47ff-841a-6772a9c302c8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_IntegrableNormPowMulExpNegMulNormSq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_continuous
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_fa1Mono_norm_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_integrable_of_norm_le_gaussian

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open MeasureTheory
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution {g : ℕ} (α : Fin g →₀ ℕ) {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : EuclideanSpace ℂ (Fin g) => ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2)) := by
  have hcont : Continuous fun z : EuclideanSpace ℂ (Fin g) =>
      ‖monomialOfMultiindex α z‖ ^ 2 * Real.exp (-b * ‖z‖ ^ 2) :=
    ((fa1Mono_continuous α).norm.pow 2).mul
      (Real.continuous_exp.comp (continuous_const.mul (continuous_norm.pow 2)))
  refine integrable_of_norm_le_gaussian hcont (2 * ∑ i, α i) hb (C := 1) fun z => ?_
  rw [one_mul, Real.norm_eq_abs, abs_of_nonneg (by positivity), pow_mul']
  have h1 := fa1Mono_norm_le α z
  gcongr
end ReciprocityTheory.ChartRestriction.G.I2
