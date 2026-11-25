-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.contDiffAt_of_punct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:19:54.598176+00:00
-- url     : https://prove2.me/submissions/d7593db7-49d6-4d4d-8423-95e8b3ebad79

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.HE
open ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric Filter Complex
open scoped ContDiff ComplexConjugate Matrix
noncomputable section
variable {n : ℕ}
variable {U : Set (V n)}
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.HE
theorem _root_.solution (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U)
    {y : V n} (hy : y ∈ U) : ContDiffAt ℂ ∞ g y := (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n g U hU hg).contDiffAt (hU.mem_nhds hy)
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
