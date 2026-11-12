-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_mapDensity_product
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:12:27.825696+00:00
-- url     : https://prove2.me/submissions/5ac8e1de-7f5f-4c72-a0c9-0362ff1b2169

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Semantics_DensityOperator_ext_toOperator


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
    (port : LogicalSite m w) (rho : DensityOperator (LogicalRegister m w))
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    (decodedRetryPoolSuccessorCoordinateBranchChannel
      m w z q stage hstage port).mapDensity
        (tensorPowerRegisterProductDensity (LogicalSite m w) rho rhoUnit
          (decodedRetryPoolBackwardSchedule m w z q stage)) =
      (tensorPowerQubitRegisterTransport (PhysicalSite m w)
        (decodedRetryPoolBackwardAttempts m w z q
          ⟨stage.1 + 1, hstage⟩)).symm.conjDensity
        ((decodedRetryPoolSuccessorPortRecordTransport
          m w z q stage hstage).conjDensity
          ((decodedRetryPoolQubitTensorPowerFinRegisterTransport
            (decodedRetryPoolBackwardSchedule m w z q stage)).conjDensity
            (tensorPowerProductInput
              ((decodedRetryPoolQubitRegisterCoordinateChannel
                (LogicalSite m w) port).mapDensity rho)
              rhoUnit (decodedRetryPoolBackwardSchedule m w z q stage)))) := by
  rw [decodedRetryPoolSuccessorCoordinateBranchChannel,
    QuantumChannel.comp_mapDensity,
    decodedRetryPoolSuccessorCoordinateTensorChannel_mapDensity_product]
  apply DensityOperator.ext_toOperator
  rfl
end QEC.Distillation.HH18Parameterized
