-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_add_const
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:49.97779+00:00
-- url     : https://prove2.me/submissions/c9cdca15-6e1f-4193-8031-13f1ffe0c194

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_DetUpdateColEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpaCHessComp
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_CommFderivApply
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_CmpbHessAtAddConst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Complex ComplexConjugate
open scoped ContDiff ENNReal ComplexOrder
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
noncomputable section
universe u
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (g : V n → ℂ) (c : ℂ) (x : V n) :
    cHess n (fun v => g v + c) x = cHess n g x := by
  have h : ∀ k, wdb n k (fun v => g v + c) = wdb n k g := by
    intro k; funext y; simp only [wdb, fderiv_add_const]
  ext j k
  simp only [cHess, Matrix.of_apply, h]
end ReciprocityTheory.L2DbarEstimates.Y
