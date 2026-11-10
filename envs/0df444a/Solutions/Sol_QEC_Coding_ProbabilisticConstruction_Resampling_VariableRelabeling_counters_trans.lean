-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.counters_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:44:15.41239+00:00
-- url     : https://prove2.me/submissions/993e9c86-6a4e-48f3-b8ce-a112069608ff

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_counters_conjugacy

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
theorem _root_.solution [Fintype D] [DecidableEq D] (v : D ≃ A) (T : HTable V X) (m : ℕ) :
    counters (codedSupport (v.trans u) U) (codedBad (v.trans u) U B)
      (encodeTable v (encodeTable u T)) m=
      encodeAssignment v (encodeAssignment u (counters U B T m)) :=
  counters_conjugacy (v.trans u) U B T m
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
