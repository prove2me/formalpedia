-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.bsA_sqn_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:34:38.776797+00:00
-- url     : https://prove2.me/submissions/3650d020-0212-4ae1-8284-7d6d455ca462

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_FlatLoc
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_BStepA
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_nonneg
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_bsA_nsq_pos

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
theorem _root_.solution {la : La} {N : ℕ} {w : Fin N → ι → Y → ℂ} {y : Y}
    (h : ∃ k, w k (A.pick y) y ≠ 0) : 0 < A.sqn la w y := by
  obtain ⟨k, hk⟩ := h
  show 0 < ∑ k, A.nsq la (w k) y
  exact Finset.sum_pos' (fun m _ => bsA_nsq_nonneg A la (w m) y) ⟨k, Finset.mem_univ _, bsA_nsq_pos A hk⟩
end ReciprocityTheory.L2DbarEstimates.Y
