-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchRouteTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:47:36.308201+00:00
-- url     : https://prove2.me/submissions/6ce27f03-d1c3-4494-8269-061b6228919c

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
attribute [local instance] QEC.Distillation.HH18Parameterized.instSuccessorBranchClassicalDecidable
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (x : tensorPowerCarrier QubitSpace
      (decodedRetryPoolBackwardSchedule m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchRouteTransport
        m w z q stage hstage x =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm
        (decodedRetryPoolSuccessorPortRecordTransport m w z q stage hstage
          (decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage) x)) := by
  rfl
end QEC.Distillation.HH18Parameterized
