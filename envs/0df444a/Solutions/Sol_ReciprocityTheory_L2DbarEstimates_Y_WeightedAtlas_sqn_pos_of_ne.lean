-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas.sqn_pos_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:58.848484+00:00
-- url     : https://prove2.me/submissions/6ba2d314-ab57-49d0-93fd-a583185424b6

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_ZLocLower
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_SetLIntegralBiUnionLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_WeightedAtlas_nsq_nonneg


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
theorem _root_.solution (A : WeightedAtlas n Y ι La) {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ}
    {y : Y} (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  have h0 : 0 < A.nsq la (w k) y := by
    unfold nsq
    have := norm_pos_iff.2 hk
    positivity
  exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun j => A.nsq la (w j) y)
    (fun j _ => A.nsq_nonneg la (w j) y) (Finset.mem_univ k))
end ReciprocityTheory.L2DbarEstimates.Y.WeightedAtlas
