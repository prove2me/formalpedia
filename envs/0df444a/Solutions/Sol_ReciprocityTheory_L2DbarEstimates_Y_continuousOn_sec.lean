-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.continuousOn_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:31:50.139882+00:00
-- url     : https://prove2.me/submissions/b00a28cc-09ca-47c4-8d15-2add784910fc

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_ChartSymmEventuallyEq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_LogNormSq
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ContinuousOnSec
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_LogPshAt_congr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Pointwise Matrix
noncomputable section
universe u
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y]
    [SecondCountableTopology Y] [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*}
    [AddCommGroup La] {A : WeightedAtlas n Y ι La} {la : La} {f : ι → Y → ℂ}
    (hf : A.IsSec la f) (i : ι) : ContinuousOn (f i) (A.chart i).source := by
  have h1 : ContinuousOn (f i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hf.1 i).continuousOn
    simpa only [Set.preimage_univ, Set.inter_univ] using this
  refine (h1.comp (A.chart i).continuousOn fun y hy => (A.chart i).map_source hy).congr
    fun y hy => ?_
  simp only [Function.comp_apply, (A.chart i).left_inv hy]
end ReciprocityTheory.L2DbarEstimates.Y
