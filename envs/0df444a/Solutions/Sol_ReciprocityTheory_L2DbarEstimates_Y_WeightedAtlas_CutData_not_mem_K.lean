-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData.not_mem_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:31:15.532284+00:00
-- url     : https://prove2.me/submissions/ac02e9b8-7f1e-4947-91ee-cb5a05c0ac60

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxF
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_AApproxJ
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_CutData_K_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open MeasureTheory Filter Topology Complex Metric Set
open scoped ContDiff ENNReal
noncomputable section
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
variable {n : ℕ} {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]
  (A : WeightedAtlas n Y ι La)
variable {A}
open ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
variable {Sf : Finset Y} (D : CutData A Sf)
namespace ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
theorem _root_.solution {P Q : Y} (hP : P ∈ Sf) (hQ : Q ∈ Sf) (hPQ : P ≠ Q) {y : Y}
    (hy : y ∈ D.K P) : y ∉ D.K Q := fun h =>
  Set.disjoint_left.1 (D.disj P hP Q hQ hPQ) (D.K_sub hP hy).2 (D.K_sub hQ h).2
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.CutData
