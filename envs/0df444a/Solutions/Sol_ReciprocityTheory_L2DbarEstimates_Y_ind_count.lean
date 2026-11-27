-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.Y.ind_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:30:31.944513+00:00
-- url     : https://prove2.me/submissions/98706caa-d9f0-43e7-87f1-06e6f63c2290

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_GROWCountStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_IndCount
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_mem_multiLe_iff
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Y_card_multiLe_succ

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
theorem _root_.solution : INDCountStatement := by
  unfold INDCountStatement
  intro n
  induction n with
  | zero =>
    intro j
    have h : multiLe 0 j = {finZeroElim} := by
      ext α
      simp only [mem_multiLe_iff, Finset.mem_singleton, Fin.sum_univ_zero]
      exact ⟨fun _ => funext fun i => i.elim0, fun _ => Nat.zero_le _⟩
    rw [h, Finset.card_singleton]
    simp
  | succ n ih =>
    intro j
    induction j with
    | zero =>
      rw [card_multiLe_succ, Finset.sum_range_one, ih]
      simp
    | succ j ihj =>
      rw [card_multiLe_succ, Finset.sum_range_succ']
      simp only [Nat.add_sub_add_right, Nat.sub_zero]
      rw [← card_multiLe_succ n j, ihj, ih (j + 1)]
      have h1 : (j + (n + 1)).choose (n + 1) = (j + 1 + n).choose (n + 1) := by
        congr 1
        omega
      have h2 : (j + 1 + (n + 1)).choose (n + 1) =
          (j + 1 + n).choose n + (j + 1 + n).choose (n + 1) := by
        rw [show j + 1 + (n + 1) = (j + 1 + n) + 1 by omega]
        exact Nat.choose_succ_succ' _ _
      omega
end ReciprocityTheory.L2DbarEstimates.Y
