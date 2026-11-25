-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.setLIntegral_biUnion_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:19:22.55952+00:00
-- url     : https://prove2.me/submissions/e7a47e00-0cf4-41d9-98ea-9a975ffbb7bd

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe

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
theorem _root_.solution {α κ : Type*} [MeasurableSpace α] (μ : Measure α)
    (F : Finset κ) (U : κ → Set α) (G : α → ℝ≥0∞) :
    ∫⁻ y in ⋃ P ∈ F, U P, G y ∂μ ≤ ∑ P ∈ F, ∫⁻ y in U P, G y ∂μ := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | insert a F ha ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (lintegral_union_le _ _ _).trans (add_le_add le_rfl ih)
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
