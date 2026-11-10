-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_conjugacy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:42:45.97236+00:00
-- url     : https://prove2.me/submissions/4360eaee-ea4a-411c-9ebf-0bda0754b827

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_step_conjugacy

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
theorem _root_.solution (T : HTable V X) (m : ℕ) :
    counters (codedSupport u U) (codedBad u U B) (encodeTable u T) m=
      encodeAssignment u (counters U B T m) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [counters,counters,ih]; exact step_conjugacy u U B T _
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
