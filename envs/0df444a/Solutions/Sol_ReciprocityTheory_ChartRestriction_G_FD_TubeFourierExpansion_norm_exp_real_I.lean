-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion.norm_exp_real_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:59:57.698359+00:00
-- url     : https://prove2.me/submissions/953d84ed-fddf-4afe-a6d9-288f0b2bee4d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeSummability
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TubeFourierExpansion

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
open Complex MeasureTheory Metric ReciprocityTheory.L2DbarEstimates.Y ReciprocityTheory.ChartRestriction.G.FD.TubeSummability
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
theorem _root_.solution (c : ℝ) (k : Fin n → ℤ) (x0 : Fin n → ℝ) :
    ‖cexp (c * I * ∑ j, (k j : ℂ) * (x0 j : ℂ))‖ = 1 := by
  have e : (c : ℂ) * I * ∑ j, (k j : ℂ) * (x0 j : ℂ) =
      ((c * ∑ j, (k j : ℝ) * x0 j : ℝ) : ℂ) * I := by
    push_cast
    ring
  rw [e, Complex.norm_exp_ofReal_mul_I]
end ReciprocityTheory.ChartRestriction.G.FD.TubeFourierExpansion
