-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.select_map_of_enabled
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T22:33:14.195307+00:00
-- url     : https://prove2.me/submissions/03d6d370-7156-4580-9b22-7c4c16509797

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_mem_closedNeighbors
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_nil_mem_witnessPaths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_occurrenceHistory_length
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_none_iff
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_select_some_bad
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
open MeasureTheory
variable {W I K : Type*} [Fintype I] [LinearOrder I] [Fintype K] [LinearOrder K]
variable (B : I → Set W) (C : K → Set W)
variable [∀ i, DecidablePred (· ∈ B i)] [∀ k, DecidablePred (· ∈ C k)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (f : I → K)
    (hle : ∀ i j, f i ≤ f j ↔ i ≤ j)
    (hbad : ∀ i w, w ∈ C (f i) ↔ w ∈ B i)
    (henabled : ∀ k w, w ∈ C k → ∃ i, f i = k) (w : W) :
    (select B w).map f = select C w := by
  cases hb : select B w with
  | none =>
      have hc : select C w = none := (select_none_iff C w).mpr (by
        intro k hk
        obtain ⟨i, rfl⟩ := henabled k w hk
        exact (select_none_iff B w).mp hb i ((hbad i w).mp hk))
      simp only [Option.map_none, hc]
  | some i =>
      have hi : w ∈ C (f i) := (hbad i w).mpr (select_some_bad B hb)
      cases hc : select C w with
      | none => exact False.elim ((select_none_iff C w).mp hc (f i) hi)
      | some k =>
          obtain ⟨j, hj⟩ := henabled k w (select_some_bad C hc)
          have hij : i ≤ j := select_le B hb ((hbad j w).mp (hj.symm ▸ select_some_bad C hc))
          have hji : j ≤ i := (hle j i).mp (hj.symm ▸ select_le C hc hi)
          have he : i = j := le_antisymm hij hji
          simp only [Option.map_some, he, hj]
end QEC.Coding.ProbabilisticConstruction.Resampling
