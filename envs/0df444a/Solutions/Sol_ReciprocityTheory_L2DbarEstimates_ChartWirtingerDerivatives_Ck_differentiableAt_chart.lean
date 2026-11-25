-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives.Ck.differentiableAt_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:02:34.717247+00:00
-- url     : https://prove2.me/submissions/3afea380-a612-46cb-be2f-0af875ed5870

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_DifferentiableAtChart
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_ChartWirtingerDerivatives_chart_mem_target

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
open ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
open Filter Topology Set
open scoped ContDiff
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
namespace Ck
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n)
    (f : M → ℂ) (hf : Ck n z 1 f) (e : OpenPartialHomeomorph M (V n)) (he : IsChart n z e)
    (x : M) (hx : x ∈ e.source) :
    DifferentiableAt ℝ (f ∘ e.symm) (z x) :=
  ((hf e he).contDiffAt (e.open_target.mem_nhds (chart_mem_target n z e he x hx))).differentiableAt
    (by simp)
end Ck
end ReciprocityTheory.L2DbarEstimates.ChartWirtingerDerivatives
