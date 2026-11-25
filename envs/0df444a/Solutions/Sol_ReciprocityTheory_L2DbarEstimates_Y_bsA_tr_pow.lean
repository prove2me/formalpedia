-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_tr_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:56:07.102655+00:00
-- url     : https://prove2.me/submissions/b359f1db-c20f-4220-bfb6-bb6d073cde20

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_g_nsmul

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
theorem _root_.solution {la : La} {U : Set Y} {a : ι → Y → ℂ} (ha : bsTr A la U a) (k : ℕ) :
    bsTr A (k • la) U (fun i y => a i y ^ k) := by
  unfold bsTr at ha ⊢
  intro i j y hy hi hj
  show a i y ^ k = A.g (k • la) i j y * a j y ^ k
  rw [ha i j y hy hi hj, bsA_g_nsmul A la k hi hj, mul_pow]
end ReciprocityTheory.L2DbarEstimates.Y
