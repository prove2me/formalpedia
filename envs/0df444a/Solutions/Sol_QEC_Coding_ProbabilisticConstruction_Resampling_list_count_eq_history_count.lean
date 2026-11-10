-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.list_count_eq_history_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:29:34.697017+00:00
-- url     : https://prove2.me/submissions/8bc14e3a-b698-42f2-bd1e-ff9bf77ccd48

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Mathlib.Data.Fintype.Fin
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_OccurrenceCounting
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open scoped BigOperators
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (root i : I) (L : List I) :
    L.count i = ((Finset.range L.length).filter (fun k => historyLabel root L k = i)).card := by
  let v : List.Vector I L.length := ⟨L, rfl⟩
  have hc := Fin.card_filter_univ_eq_vector_get_eq_count i v
  change _ = L.count i at hc
  rw [← hc]
  apply Finset.card_bij (fun k _ => k.val)
  · intro k hk
    obtain ⟨_, he⟩ := Finset.mem_filter.mp hk
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr k.isLt, ?_⟩
    change L[k.val] = i at he
    simpa only [historyLabel, List.getElem?_eq_getElem k.isLt, Option.getD_some] using he
  · intro a ha b hb he; exact Fin.ext he
  · intro k hk
    obtain ⟨hk, he⟩ := Finset.mem_filter.mp hk
    refine ⟨⟨k, Finset.mem_range.mp hk⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    have hkl : k < L.length := Finset.mem_range.mp hk
    change L[k] = i
    simpa only [historyLabel, List.getElem?_eq_getElem (Finset.mem_range.mp hk),
      Option.getD_some] using he
end QEC.Coding.ProbabilisticConstruction.Resampling
