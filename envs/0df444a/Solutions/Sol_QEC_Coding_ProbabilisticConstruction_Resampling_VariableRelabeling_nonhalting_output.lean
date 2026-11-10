-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.nonhalting_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:50:23.892172+00:00
-- url     : https://prove2.me/submissions/c70dfe9f-a2b9-44a3-b927-dba730d32a92

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_output_conjugacy

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
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
theorem _root_.solution (T : HTable V X) (h : ¬Halts U B T) :
    output (codedSupport u U) (codedBad u U B) (encodeTable u T)=
      fun a => T (u a,0) := by
  have hz : haltTime (X := fun _ : V => X) U B T=0 := by
    unfold haltTime
    exact dif_neg h
  rw [output_conjugacy]
  funext a
  change T (u a,counters U B T (haltTime U B T) (u a))=T (u a,0)
  exact congrArg (fun n : ℕ => T (u a,counters U B T n (u a))) hz
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
