-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.table_tests_probability
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:43.417188+00:00
-- url     : https://prove2.me/submissions/ac6c0549-527b-4f96-82ec-5f4877a0a950

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_familyRead
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_familyRead_law
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_mem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_advance_of_notMem
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_notMem
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (coords : A → Finset V) (column : ∀ a, coords a → ℕ)
    (haddress : Function.Injective
      (fun s : (a : A) × coords a => (s.2.val, column s.1 s.2)))
    (test : ∀ a, Set (∀ v : coords a, X v)) (htest : ∀ a, MeasurableSet (test a)) :
    tableLaw ν {R | ∀ a, familyRead coords column R a ∈ test a} =
      ∏ a, (Measure.pi (fun v : coords a => ν v)) (test a) := by
  have hm := measurable_familyRead (X := X) coords column
  have hset : {R | ∀ a, familyRead coords column R a ∈ test a} =
      familyRead coords column ⁻¹' Set.univ.pi test := by ext R; simp
  rw [hset, ← Measure.map_apply hm (MeasurableSet.univ_pi htest),
    familyRead_law ν coords column haddress, Measure.pi_pi]
end QEC.Coding.ProbabilisticConstruction.Resampling
