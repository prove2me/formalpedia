-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.closIneq_norm_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:43:35.262952+00:00
-- url     : https://prove2.me/submissions/3c3ae7c3-958c-4827-a2ac-b4a2c31bf71d

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_Closure
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_closIneq_sq_le

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
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] (x y : E) (η : ℝ) (hη : 0 < η) :
    ‖x + y‖ ^ 2 ≤ (1 + η) * ‖x‖ ^ 2 + (1 + η⁻¹) * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := by
    nlinarith [norm_nonneg (x + y), norm_nonneg x, norm_nonneg y]
  exact h2.trans (closIneq_sq_le _ _ η hη)
end ReciprocityTheory.L2DbarEstimates.F
