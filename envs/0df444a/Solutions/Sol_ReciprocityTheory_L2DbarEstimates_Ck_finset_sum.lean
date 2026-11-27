-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Ck.finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:29:56.181411+00:00
-- url     : https://prove2.me/submissions/7a0d4f90-3df4-499c-9be4-0701426eba92

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_MeasurableSetImageOfIsLocalHomeomorph
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ExistsChartPartition
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_IntegralFderivApplyEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open MeasureTheory Filter Topology Set
open scoped ContDiff ENNReal
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) {ι : Type*}
    (s : Finset ι) (F : ι → M → ℂ) (hF : ∀ i, Ck n z 1 (F i)) :
    Ck n z 1 (fun y => ∑ i ∈ s, F i y) := by
  intro e he
  exact ContDiffOn.sum fun i _ => hF i e he
end Ck
end ReciprocityTheory.L2DbarEstimates
