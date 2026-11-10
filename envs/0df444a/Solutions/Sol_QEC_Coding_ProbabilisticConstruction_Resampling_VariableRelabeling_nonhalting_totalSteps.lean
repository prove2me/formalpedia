-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.nonhalting_totalSteps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:49:05.912031+00:00
-- url     : https://prove2.me/submissions/b792bccd-d43a-4b6a-8e8f-5d0d9cbe92ea

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_totalSteps_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_halts_of_totalSteps_lt_top


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
    totalSteps U B T=∞ ∧
      totalSteps (codedSupport u U) (codedBad u U B) (encodeTable u T)=∞ := by
  have ht : totalSteps U B T=∞ := by
    by_contra hn
    have hf : totalSteps (X := fun _ : V => X) U B T < (∞ : ℝ≥0∞) :=
      lt_top_iff_ne_top.mpr hn
    have hh : Halts (X := fun _ : V => X) U B T :=
      @halts_of_totalSteps_lt_top I V inferInstance inferInstance inferInstance inferInstance
        (fun _ : V => X) (fun _ : V => (⊥ : MeasurableSpace X)) U B inferInstance T hf
    exact h hh
  exact ⟨ht,(totalSteps_conjugacy u U B T).trans ht⟩
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
