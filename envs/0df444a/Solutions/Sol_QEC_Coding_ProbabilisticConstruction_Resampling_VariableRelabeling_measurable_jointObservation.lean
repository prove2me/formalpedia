-- Prove2me | solution 1 for QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling.measurable_jointObservation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-09T19:39:07.963199+00:00
-- url     : https://prove2.me/submissions/a82c80b7-da88-4547-baec-298c7e6368f7

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_Termination
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_TableProbability
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_nat_prefixCount
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurableSet_halts
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_counters
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_haltTime
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_output
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_selected
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalCount
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_totalSteps


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
theorem _root_.solution (hB : ∀ i, MeasurableSet (B i)) :
    Measurable (jointObservation (X := X) U B) := by
  have hc : Measurable (fun T : HTable V X => counters U B T) :=
    measurable_pi_lambda _ (fun m => measurable_counters (X := fun _ : V => X) U B hB m)
  have hs : Measurable (fun T : HTable V X => selected U B T) :=
    measurable_pi_lambda _ (fun m => measurable_selected (X := fun _ : V => X) U B hB m)
  have hh : Measurable (fun T : HTable V X => if Halts U B T then true else false) :=
    Measurable.ite (measurableSet_halts (X := fun _ : V => X) U B hB) measurable_const measurable_const
  have hp : Measurable (fun T : HTable V X => prefixCount U B T) :=
    measurable_pi_lambda _ (fun m => measurable_pi_lambda _ (fun i => measurable_nat_prefixCount U B hB m i))
  have ht : Measurable (fun T : HTable V X => totalCount U B T) :=
    measurable_pi_lambda _ (fun i => measurable_totalCount (X := fun _ : V => X) U B hB i)
  exact hc.prodMk (hs.prodMk (hh.prodMk ((measurable_haltTime (X := fun _ : V => X) U B hB).prodMk
    ((measurable_output (X := fun _ : V => X) U B hB).prodMk (hp.prodMk (ht.prodMk (measurable_totalSteps (X := fun _ : V => X) U B hB)))))))
end QEC.Coding.ProbabilisticConstruction.Resampling.VariableRelabeling
