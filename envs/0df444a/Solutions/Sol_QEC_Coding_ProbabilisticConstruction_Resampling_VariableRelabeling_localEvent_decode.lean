-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.localEvent_decode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:36:45.393195+00:00
-- url     : https://prove2.me/submissions/80ac90eb-5a05-47b7-9bd4-fb87cb99aa48

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_restriction_decode

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.ProbabilisticConstruction QEC.Coding.ProbabilisticConstruction.Resampling QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
open MeasureTheory ProbabilityTheory
open scoped Classical BigOperators ENNReal
variable {V A D I X : Type*}
variable [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A]
variable [Fintype I] [LinearOrder I]
namespace QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
theorem _root_.solution (u : A ≃ V) (U : I → Finset V)
    (B : ∀ i, Set (U i → X)) (i : I) (z : A → X) :
    z∈localEvent (codedSupport u U) (codedBad u U B) i ↔
      decodeAssignment u z∈localEvent U B i := by
  change decodeLocal u U i ((codedSupport u U i).restrict z)∈B i ↔ _
  rw [restriction_decode]
  rfl
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
