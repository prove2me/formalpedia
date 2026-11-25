-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.FPw.ell_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:07:57.2344+00:00
-- url     : https://prove2.me/submissions/cca2b45b-06e2-4e6e-b741-0cbfaefb2465

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_PaIPZeroRight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_IteratedFDerivTailZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_FourierProjections_ExpNEllMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2 ReciprocityTheory.ChartRestriction.G.I2.FPw
open MeasureTheory Complex Filter Topology
noncomputable section
variable {ι : Type} [Fintype ι]
open Classical
namespace ReciprocityTheory.ChartRestriction.G.I2.FPw
theorem _root_.solution (q : ℕ) (a v : EuclideanSpace ℂ ι) : ‖ellL q a v‖ ≤ q * Real.pi * (‖a‖ * ‖v‖) := by
  unfold ellL
  rw [ContinuousLinearMap.smul_apply, norm_smul]
  have h1 : ‖((innerSL ℂ) a) v‖ ≤ ‖a‖ * ‖v‖ := norm_inner_le_norm (𝕜 := ℂ) a v
  have h2 : ‖((q : ℂ) * (Real.pi : ℂ))‖ = q * Real.pi := by
    rw [norm_mul, Complex.norm_natCast, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [h2]
  exact mul_le_mul_of_nonneg_left h1 (by positivity)
end ReciprocityTheory.ChartRestriction.G.I2.FPw
