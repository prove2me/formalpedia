-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.advance_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:10:15.644981+00:00
-- url     : https://prove2.me/submissions/5b4c5c2c-e43d-4a23-af73-00839fadb70d

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_LocalLemma
import Mathlib.Probability.ProductMeasure
import Mathlib.Data.Finset.Sort
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Execution
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_empty
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_avoid_insert
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_empty
attribute [local simp] QEC.Coding.ProbabilisticConstruction.avoid_insert



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [LinearOrder I]
variable {X : V → Type*}
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (vars : I → Finset V) (i : I) (c : Counters V)
    {v : V} (hv : v ∈ vars i) : advance vars i c v = c v + 1 := by
  simp [advance, hv]
end QEC.Coding.ProbabilisticConstruction.Resampling
