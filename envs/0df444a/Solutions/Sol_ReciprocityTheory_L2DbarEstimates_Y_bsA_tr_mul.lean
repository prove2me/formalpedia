-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_tr_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:25:43.363572+00:00
-- url     : https://prove2.me/submissions/623aa030-5806-4bb5-8d15-fd5d85a670de

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA

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
theorem _root_.solution {la mu : La} {U : Set Y} {a b : ι → Y → ℂ} (ha : bsTr A la U a)
    (hb : bsTr A mu U b) : bsTr A (la + mu) U (fun i y => a i y * b i y) := by
  unfold bsTr at ha hb ⊢
  intro i j y hy hi hj
  show a i y * b i y = A.g (la + mu) i j y * (a j y * b j y)
  rw [ha i j y hy hi hj, hb i j y hy hi hj, A.g_add la mu i j y hi hj]
  ring
end ReciprocityTheory.L2DbarEstimates.Y
