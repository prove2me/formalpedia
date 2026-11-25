-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuousOn_sec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:18:07.536751+00:00
-- url     : https://prove2.me/submissions/eb3100a5-7994-4d24-8f67-e48fa325e184

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FamilyLeCoords
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_JacobianInterpolationStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_LintegralBallRpowLtTop

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
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {s : ι → Y → ℂ} (hs : A.IsSec la s)
    (i : ι) : ContinuousOn (s i) (A.chart i).source := by
  have h1 : ContinuousOn (s i ∘ (A.chart i).symm) (A.chart i).target := by
    have := (hs.1 i).continuousOn
    simpa [Set.preimage_univ, Set.inter_univ] using this
  have h2 : ContinuousOn ((s i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
