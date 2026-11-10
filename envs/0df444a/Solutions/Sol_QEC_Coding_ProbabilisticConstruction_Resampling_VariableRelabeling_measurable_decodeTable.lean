-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_decodeTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:36:50.598622+00:00
-- url     : https://prove2.me/submissions/5978698b-d009-4440-b265-36b9a6bbb965

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_encodeTable

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]
variable (u : A ≃ V) (U : I → Finset V) (B : ∀ i, Set (U i → X))
variable [∀ i, DecidablePred (·∈B i)]
variable [MeasurableSpace X] [MeasurableSpace I] [MeasurableSingletonClass I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
theorem _root_.solution : Measurable (decodeTable (X := X) u) :=
  measurable_encodeTable u.symm
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
