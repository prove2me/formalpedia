-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.HE.isOpen_punct
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:30:36.204812+00:00
-- url     : https://prove2.me/submissions/4d3170c1-0c2b-488d-ab15-63928e46bbf0

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_SkodaWeights_LeviVA
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_DerivDerivNonposOfIsLocalMax
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_HoloSmooth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfE

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
theorem _root_.solution (hU : IsOpen U) {g : V n → ℂ} (hg : DifferentiableOn ℂ g U) :
    IsOpen {y | y ∈ U ∧ g y ≠ 0} := hg.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
end ReciprocityTheory.ChartRestriction.G.AR.Up.HE
