-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.mem_multiLe_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:36:37.898458+00:00
-- url     : https://prove2.me/submissions/a7f1268d-af3d-4fff-bfbc-e47ef8a840a3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount

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
universe u
open Finset
namespace ReciprocityTheory.L2DbarEstimates.Y
theorem _root_.solution {n j : ℕ} {α : Fin n → ℕ} : α ∈ multiLe n j ↔ ∑ i, α i ≤ j := by
  unfold multiLe
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨a, ha, hα⟩
    rw [Finset.mem_range] at ha
    rw [Nat.mem_antidiagonalTuple] at hα
    omega
  · intro h
    exact ⟨∑ i, α i, Finset.mem_range.2 (by omega), Nat.mem_antidiagonalTuple.2 rfl⟩
end ReciprocityTheory.L2DbarEstimates.Y
