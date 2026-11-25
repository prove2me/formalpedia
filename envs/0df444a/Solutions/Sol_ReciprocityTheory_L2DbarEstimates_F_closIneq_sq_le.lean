-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:14.509658+00:00
-- url     : https://prove2.me/submissions/58829ed5-f19e-4f8b-9c40-94db32a4b572

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (a b η : ℝ) (hη : 0 < η) :
    (a + b) ^ 2 ≤ (1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2 := by
  have hi : η * η⁻¹ = 1 := mul_inv_cancel₀ hη.ne'
  have key : η * ((1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2) - η * (a + b) ^ 2 = (η * a - b) ^ 2 := by
    linear_combination b ^ 2 * hi
  have h2 : η * (a + b) ^ 2 ≤ η * ((1 + η) * a ^ 2 + (1 + η⁻¹) * b ^ 2) := by
    nlinarith [key, sq_nonneg (η * a - b)]
  exact le_of_mul_le_mul_left h2 hη
end ReciprocityTheory.L2DbarEstimates.F
