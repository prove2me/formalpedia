-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.trans_contDiffOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:16:08.891942+00:00
-- url     : https://prove2.me/submissions/a0a7b81b-9e52-460b-8924-0b5c7d2a7d62

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxC
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxD
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_isOpen_ovl
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_contDiffOn_of_differentiableOn


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (j i : ι) :
    ContDiffOn ℂ ∞ ((A.chart i) ∘ (A.chart j).symm) (ovl A.chart j i) := by
  refine contDiffOn_piLp' 2 fun k => ?_
  have h : DifferentiableOn ℂ (fun x => ((A.chart i) ((A.chart j).symm x)) k) (ovl A.chart j i) :=
    (EuclideanSpace.proj k : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn (A.holo_trans j i)
  exact ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ (A.isOpen_ovl j i) h
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
