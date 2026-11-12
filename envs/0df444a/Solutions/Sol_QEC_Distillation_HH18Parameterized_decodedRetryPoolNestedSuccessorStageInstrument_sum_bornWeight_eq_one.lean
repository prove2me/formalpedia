-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolNestedSuccessorStageInstrument_sum_bornWeight_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:50:09.132692+00:00
-- url     : https://prove2.me/submissions/2b98e5a3-d6d7-4b2f-a13b-4628b1eecb99

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_StageTransition
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_Power
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_NestedSuccessorStage
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorStageInstrument_complete
import Theorems.Thm_QEC_Semantics_FiniteInstrument_nestedTensorPower_sum_bornWeight_eq_one


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
    (z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (rho : DensityOperator
      (nestedTensorCarrier
        (QubitRegister (decodedRetryPoolSuccessorSourceSlots m w z q stage))
        (logicalOutputCount m w) stage.1)) :
    ∑ outcome,
        (decodedRetryPoolNestedSuccessorStageInstrument
          h hdegree z q stage hstage).bornWeight outcome rho = 1 := by
  exact nestedTensorPower_sum_bornWeight_eq_one
    (decodedRetryPoolSuccessorStageInstrument h hdegree z q stage hstage)
    (decodedRetryPoolSuccessorStageInstrument_complete h hdegree z q stage hstage)
    (logicalOutputCount m w) stage.1 rho
end QEC.Distillation.HH18Parameterized
