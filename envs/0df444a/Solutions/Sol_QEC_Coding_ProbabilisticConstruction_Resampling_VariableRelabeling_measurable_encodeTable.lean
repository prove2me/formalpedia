-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_encodeTable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:34:34.602625+00:00
-- url     : https://prove2.me/submissions/6ded29a0-0da3-47d9-ac0e-1b8195077bc6

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling

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
theorem _root_.solution : Measurable (encodeTable (X := X) u) :=
  measurable_pi_lambda _ (fun p => measurable_pi_apply (u p.1,p.2))
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
