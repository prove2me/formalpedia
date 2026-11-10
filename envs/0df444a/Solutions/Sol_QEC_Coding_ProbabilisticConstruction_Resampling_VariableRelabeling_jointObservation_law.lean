-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.jointObservation_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:54:14.310491+00:00
-- url     : https://prove2.me/submissions/31d7c728-4674-433f-ad3a-b7bb6602f31f

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_encodeTable
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_table_law
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_jointObservation_conjugacy
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodedObservation

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
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i))
    (ν : V → Measure X) [∀ v, IsProbabilityMeasure (ν v)] :
    (tableLaw (fun a => ν (u a))).map (decodedObservation u U B)=
      (tableLaw ν).map (jointObservation U B) := by
  have h := congrArg (fun μ => μ.map (decodedObservation u U B)) (table_law u ν)
  rw [Measure.map_map (measurable_decodedObservation u U B hB) (measurable_encodeTable u)] at h
  have he : (decodedObservation u U B) ∘ encodeTable u=jointObservation U B :=
    funext (jointObservation_conjugacy u U B)
  rw [he] at h
  exact h.symm
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
