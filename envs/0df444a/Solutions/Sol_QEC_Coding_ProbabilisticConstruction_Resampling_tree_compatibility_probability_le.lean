-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.tree_compatibility_probability_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:29:50.343081+00:00
-- url     : https://prove2.me/submissions/24188616-ba4c-49bc-8c57-f4220cba9181

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ExecutionWitness
import Mathlib.Data.ENNReal.BigOperators
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TreeProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_witnessWeight_eq_prod_paths
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_eventProbability_nonneg
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_ofReal_eventProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_compatibility_probability_le
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
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (G : SimpleGraph I) [DecidableRel G.Adj]
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
variable (bad : ∀ i, Set (∀ v : vars i, X v))
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (hbad : ∀ i, MeasurableSet (bad i))
    (h : ℕ) (i : I) (t : WitnessTree (supportGraph vars) h i) :
    tableLaw ν (compatible vars bad i (witnessPaths (supportGraph vars) h i t)) ≤
      ENNReal.ofReal (witnessWeight (supportGraph vars) (eventProbability vars ν bad) h i t) := by
  have hb := compatibility_probability_le vars ν bad hbad i
    (witnessPaths (supportGraph vars) h i t)
  rw [witnessWeight_eq_prod_paths, ENNReal.ofReal_prod_of_nonneg
    (fun q _ => eventProbability_nonneg vars ν bad _)]
  simp only [ofReal_eventProbability]
  exact hb.trans_eq (Finset.prod_coe_sort
    (witnessPaths (supportGraph vars) h i t)
    (fun p => (Measure.pi ν) (localEvent vars bad (pathLabel i p))))
end QEC.Coding.ProbabilisticConstruction.Resampling
