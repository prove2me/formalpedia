-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_ph_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:32:42.08653+00:00
-- url     : https://prove2.me/submissions/e29efdb4-98aa-48c2-958d-43ef2c63c273

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
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
open scoped ContDiff ENNReal
noncomputable section
universe u
variable {n : ℕ} {Y : Type u} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution (la : La) (i : ι) : ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 := (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun z hz => (A.chart i).map_source hz)
  refine h2.congr ?_
  intro z hz
  simp only [Function.comp_apply, (A.chart i).left_inv hz]
end ReciprocityTheory.L2DbarEstimates.Y
