-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:25:39.847017+00:00
-- url     : https://prove2.me/submissions/279b8bd4-1e47-411f-bfbc-bbf186eb415f

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
theorem _root_.solution {g₁ g₂ : V n → ℂ} {x : V n} (h : g₁ =ᶠ[𝓝 x] g₂) :
    cHess n g₁ x = cHess n g₂ x := by
  have hw : ∀ k, wdb n k g₁ =ᶠ[𝓝 x] wdb n k g₂ := by
    intro k
    have hn : ∀ᶠ y in 𝓝 x, g₁ =ᶠ[𝓝 y] g₂ := by
      first
      | exact h.eventuallyEq_nhds
      | exact h.eventually_nhds
    filter_upwards [hn] with y hy
    simp only [wdb, hy.fderiv_eq]
  ext j k
  simp only [cHess, Matrix.of_apply, wd, (hw k).fderiv_eq]
end ReciprocityTheory.L2DbarEstimates.Y
