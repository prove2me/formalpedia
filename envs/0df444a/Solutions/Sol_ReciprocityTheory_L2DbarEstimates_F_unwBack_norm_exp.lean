-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.unwBack_norm_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:36:13.897855+00:00
-- url     : https://prove2.me/submissions/f20ab001-cd57-43ae-8705-b57df6d4c345

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackA

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
theorem _root_.solution (a : ℝ) : ‖(Real.exp a : ℂ)‖ = Real.exp a := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos a)]
end ReciprocityTheory.L2DbarEstimates.F
