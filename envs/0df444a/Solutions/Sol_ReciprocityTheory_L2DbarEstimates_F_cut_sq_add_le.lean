-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.cut_sq_add_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:09:04.992698+00:00
-- url     : https://prove2.me/submissions/acce0e1f-146b-4a8d-b467-955640e21e6b

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_CutoffA

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
theorem _root_.solution {E : Type*} [SeminormedAddCommGroup E] (a b : E) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    first
    | exact pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
    | (gcongr; exact norm_add_le a b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
end ReciprocityTheory.L2DbarEstimates.F
