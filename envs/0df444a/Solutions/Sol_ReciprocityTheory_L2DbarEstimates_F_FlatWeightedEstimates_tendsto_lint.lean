-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates.tendsto_lint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:33:26.193139+00:00
-- url     : https://prove2.me/submissions/331356d0-68c8-479c-9a70-89e527f24f5c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Mollifiers_MollifierL2LocTendsto
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_IntegrableFd
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_FlatWeightedEstimates_lint_sq

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
open ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
namespace ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
theorem _root_.solution {ι α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] {l : Filter ι}
    {μ : Measure α} (F : ι → α → E) (h : Tendsto (fun i => eLpNorm (F i) 2 μ) l (𝓝 0)) :
    Tendsto (fun i => ∫⁻ x, ‖F i x‖ₑ ^ 2 ∂μ) l (𝓝 0) := by
  simp_rw [lint_sq]
  simpa using ENNReal.Tendsto.pow (n := 2) h
end ReciprocityTheory.L2DbarEstimates.F.FlatWeightedEstimates
