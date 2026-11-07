-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.finiteRestriction_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:42:16.028365+00:00
-- url     : https://prove2.me/submissions/d0192751-79b7-4efd-a15b-78e13398b045

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
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
theorem _root_.solution (S : Finset V) :
    (Measure.pi ν).map S.restrict = Measure.pi (fun v : S => ν v) := by
  have h := Measure.map_infinitePi_infinitePi_of_inj
    (P := ν) (f := fun v : S => v.val) Subtype.val_injective
  simp only [Measure.infinitePi_eq_pi] at h
  change (Measure.pi ν).map (fun ω (i : S) => ω i.val) = _
  exact h
end QEC.Coding.ProbabilisticConstruction.Resampling
