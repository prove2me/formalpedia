-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.isSec_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:22.309686+00:00
-- url     : https://prove2.me/submissions/7357c066-2064-4bb2-9fa0-afbe3f51755e

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
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {κ : Type*} (F : Finset κ)
    {h : κ → ι → Y → ℂ} (hh : ∀ q ∈ F, A.IsSec la (h q)) :
    A.IsSec la (fun i y => ∑ q ∈ F, h q i y) := by
  refine ⟨fun i => ?_, fun i j y hy hi hj => ?_⟩
  · have : (fun y => ∑ q ∈ F, h q i y) ∘ (A.chart i).symm =
        fun v => ∑ q ∈ F, (h q i ∘ (A.chart i).symm) v := by
      funext v; simp
    rw [this]
    exact DifferentiableOn.fun_sum (fun q hq => (hh q hq).1 i)
  · rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q hq => (hh q hq).2 i j y hy hi hj)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
