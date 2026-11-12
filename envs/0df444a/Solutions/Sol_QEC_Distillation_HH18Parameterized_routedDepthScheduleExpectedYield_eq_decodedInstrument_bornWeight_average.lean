-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.routedDepthScheduleExpectedYield_eq_decodedInstrument_bornWeight_average
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:04:04.684121+00:00
-- url     : https://prove2.me/submissions/e5da6e0e-0cee-4b8f-8d64-4a1a9f22ba73

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_Schedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
import Theorems.Thm_QEC_Distillation_HH18Parameterized_routedDepthPooledYield_eq_sum_div_card


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open scoped BigOperators
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate)
    (hsmall : routedDepthInitialSmallDomain w r m epsilon)
    (depth : Nat) :
    (routedDepthScheduleExpectedYield h hdegree epsilon hsmall depth : ℝ) =
      (∑ path : routedDepthOutputSlots m w depth,
        ∏ stage : Fin depth,
          (decodedInstrument h hdegree).bornWeight .accepted
            (prepareMeasuredResources m w
              (noisyResources m w
                (routedDepthPathRate h hdegree epsilon hsmall stage.1
                  (routedDepthPathStagePath m w depth path stage))))) /
        Fintype.card (routedDepthOutputSlots m w depth) := by
  rw [routedDepthPooledYield_eq_sum_div_card]
  apply congrArg (fun numerator : ℝ => numerator /
    Fintype.card (routedDepthOutputSlots m w depth))
  apply Finset.sum_congr rfl
  intro path _
  exact routedDepthPathYieldFactor_eq_decodedInstrument_bornWeight_product
    h hdegree epsilon hsmall depth path
end QEC.Distillation.HH18Parameterized
