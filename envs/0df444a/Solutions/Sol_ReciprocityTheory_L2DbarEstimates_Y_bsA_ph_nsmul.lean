-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_ph_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:36:47.876525+00:00
-- url     : https://prove2.me/submissions/f1a6a38f-d7de-4ebd-9526-6f23a7dd9c09

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_ph_zero

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
theorem _root_.solution (la : La) (k : ℕ) {i : ι} {y : Y} (hi : y ∈ (A.chart i).source) :
    A.ph (k • la) i y = k * A.ph la i y := by
  induction k with
  | zero => rw [zero_nsmul, bsA_ph_zero A hi]; simp
  | succ k ih => rw [succ_nsmul, A.ph_add _ _ i y hi, ih]; push_cast; ring
end ReciprocityTheory.L2DbarEstimates.Y
