-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_g_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:31:59.368663+00:00
-- url     : https://prove2.me/submissions/65b21140-e147-480f-a0c0-c1aeae601103

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_g_zero

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
theorem _root_.solution (la : La) (k : ℕ) {i j : ι} {y : Y} (hi : y ∈ (A.chart i).source)
    (hj : y ∈ (A.chart j).source) : A.g (k • la) i j y = A.g la i j y ^ k := by
  induction k with
  | zero => rw [zero_nsmul, pow_zero]; exact bsA_g_zero A hi hj
  | succ k ih => rw [succ_nsmul, A.g_add _ _ i j y hi hj, ih, pow_succ]
end ReciprocityTheory.L2DbarEstimates.Y
