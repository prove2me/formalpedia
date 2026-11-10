-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.historyWitness_root_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:22:51.542557+00:00
-- url     : https://prove2.me/submissions/d6c5c7c9-de78-441c-aebd-5839f17588aa

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_WitnessTrees
import Mathlib.Data.Finset.Max
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_labelCount_extend_root
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root : I) (L : List I) :
    labelCount root root (historyWitness G root L) = L.count root + 1 := by
  induction L with
  | nil =>
    change (Finset.filter (fun p => pathLabel root p = root) {[]}).card = 1
    have hf : Finset.filter (fun p => pathLabel root p = root) {[]} = {[]} := by
      apply Finset.filter_eq_self.mpr
      intro p hp
      have he : p = [] := Finset.mem_singleton.mp hp
      subst p
      rfl
    rw [hf, Finset.card_singleton]
  | cons j L ih =>
    rw [historyWitness, labelCount_extend_root G root j _ (historyWitness_proper G root L).1, ih]
    by_cases he : j = root <;> simp [he, List.count_cons, Nat.add_assoc, Nat.add_comm]
end QEC.Coding.ProbabilisticConstruction.Resampling
