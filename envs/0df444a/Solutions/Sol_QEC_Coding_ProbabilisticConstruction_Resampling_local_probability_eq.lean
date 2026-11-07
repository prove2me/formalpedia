-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.local_probability_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:51:44.518375+00:00
-- url     : https://prove2.me/submissions/26696a41-7396-4767-89bc-082ebd21e140

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_finiteRestriction_law

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators
variable {V A : Type*} [Fintype V] [DecidableEq V] [Fintype A]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (ν : ∀ v, Measure (X v)) [∀ v, IsProbabilityMeasure (ν v)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (S : Finset V) (bad : Set (∀ v : S, X v))
    (hbad : MeasurableSet bad) :
    (Measure.pi ν) (S.restrict ⁻¹' bad) = (Measure.pi (fun v : S => ν v)) bad := by
  rw [← Measure.map_apply S.measurable_restrict hbad, finiteRestriction_law ν S]
end QEC.Coding.ProbabilisticConstruction.Resampling
