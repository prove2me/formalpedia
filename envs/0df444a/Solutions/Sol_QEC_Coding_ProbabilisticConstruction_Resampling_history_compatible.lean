-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.history_compatible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:28:01.5963+00:00
-- url     : https://prove2.me/submissions/e9f5a963-3893-469c-a0af-2934ad3cb597

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_HistoryCounters
import Mathlib.Data.List.OfFn
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_counters_eq_historyCounter
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_historyWitness_distinctVariableDepth
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_selected_some_bad
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_label
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_timedHistoryWitness_time_bounds
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_variableRank_eq_historyCounter
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessPartition_zero
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.mem_closedNeighbors
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.nil_mem_witnessPaths
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.witnessPartition_zero
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert


attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.occurrenceHistory_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (root : I) (L : List I)
    (hlog : ∀ k ≤ L.length, selected vars bad R k = some (historyLabel root L k)) :
    R ∈ compatible vars bad root (historyWitness (supportGraph vars) root L) := by
  classical
  refine ⟨historyWitness_distinctVariableDepth vars root L, ?_⟩
  intro q
  have hq : q.val ∈ (timedHistoryWitness (supportGraph vars) root 0 L).image Prod.fst := by
    simpa only [timedHistoryWitness_paths] using q.property
  obtain ⟨p, hp, hpq⟩ := Finset.mem_image.mp hq
  have hpt : p.2 ≤ L.length := by
    simpa using (timedHistoryWitness_time_bounds (supportGraph vars) root 0 L p hp).2
  have hlabel : pathLabel root q.val = historyLabel root L p.2 := by
    simpa [hpq] using timedHistoryWitness_label (supportGraph vars) root 0 L p hp
  have hselected : selected vars bad R p.2 = some (pathLabel root q.val) := by
    rw [hlabel]; exact hlog p.2 hpt
  have hb := selected_some_bad vars bad R p.2 (pathLabel root q.val) hselected
  change (fun v : vars (pathLabel root q.val) =>
    R (v.val, variableRank vars root (historyWitness (supportGraph vars) root L)
      q.val v.val)) ∈ bad (pathLabel root q.val)
  have he : (fun v : vars (pathLabel root q.val) =>
      R (v.val, variableRank vars root (historyWitness (supportGraph vars) root L)
        q.val v.val)) =
      (fun v : vars (pathLabel root q.val) => assignment R (counters vars bad R p.2) v.val) := by
    funext v
    have hpv : v.val ∈ vars (pathLabel root p.1) := hpq.symm ▸ v.property
    have hr := variableRank_eq_historyCounter vars root L p hp v.val hpv
    rw [hpq] at hr
    rw [hr, ← counters_eq_historyCounter vars bad R root L hlog p.2 hpt v.val]
    rfl
  rw [he]
  exact hb
end QEC.Coding.ProbabilisticConstruction.Resampling
