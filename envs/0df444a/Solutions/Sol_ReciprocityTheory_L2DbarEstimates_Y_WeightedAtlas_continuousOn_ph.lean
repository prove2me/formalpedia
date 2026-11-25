-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.continuousOn_ph
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:18:03.343827+00:00
-- url     : https://prove2.me/submissions/613709bd-eac9-411f-bbb2-e6f11fc90270

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
theorem _root_.solution (A : WeightedAtlas n Y ι La) (la : La) (i : ι) :
    ContinuousOn (A.ph la i) (A.chart i).source := by
  have h1 : ContinuousOn (A.ph la i ∘ (A.chart i).symm) (A.chart i).target :=
    (A.smooth_ph la i).continuousOn
  have h2 : ContinuousOn ((A.ph la i ∘ (A.chart i).symm) ∘ (A.chart i)) (A.chart i).source :=
    h1.comp (A.chart i).continuousOn (fun x hx => (A.chart i).map_source hx)
  refine h2.congr (fun x hx => ?_)
  simp [Function.comp, (A.chart i).left_inv hx]
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
