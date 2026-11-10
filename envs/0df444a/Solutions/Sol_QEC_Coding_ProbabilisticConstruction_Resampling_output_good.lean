-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.output_good
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:30:33.610318+00:00
-- url     : https://prove2.me/submissions/924c742d-516f-4463-b024-14fd334a14f7

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Expectation
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_haltTime_spec
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_selected_none_good


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
variable {I V : Type*} [Fintype I] [LinearOrder I] [Fintype V] [DecidableEq V]
variable {X : V → Type*} [∀ v, MeasurableSpace (X v)]
variable (vars : I → Finset V) (bad : ∀ i, Set (∀ v : vars i, X v))
variable [∀ i, DecidablePred (· ∈ bad i)]
namespace QEC.Coding.ProbabilisticConstruction.Resampling
theorem _root_.solution (R : Table (X := X)) (h : Halts vars bad R) :
    ∀ i, output vars bad R ∉ localEvent vars bad i :=
  selected_none_good vars bad R _ (haltTime_spec vars bad R h)
end QEC.Coding.ProbabilisticConstruction.Resampling
