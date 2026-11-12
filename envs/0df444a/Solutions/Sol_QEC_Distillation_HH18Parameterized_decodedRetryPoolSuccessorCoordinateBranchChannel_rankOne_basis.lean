-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorCoordinateBranchChannel_rankOne_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:17:24.083247+00:00
-- url     : https://prove2.me/submissions/34c0c773-1544-48e5-aa7a-2bfecbff5ea1

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_RecordRouting
import Definitions.Def_QEC_Semantics_Instruments_TensorPower_ChannelProductFunctorial
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_BranchProduct
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
import Theorems.Thm_QEC_Semantics_QuantumChannel_comp_apply
attribute [local simp] QEC.Semantics.QuantumChannel.comp_apply



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
    (port : LogicalSite m w)
    (left right : Bitstring
      (decodedRetryPoolSuccessorSourceSlots m w z q stage)) :
    decodedRetryPoolSuccessorCoordinateBranchChannel m w z q stage hstage port
        (decodedRetryPoolSuccessorSourceMatrixUnit
          m w z q stage left right) =
      decodedRetryPoolSuccessorCoordinateBranchCoefficient
          m w z q stage port left right •
        decodedRetryPoolSuccessorCoordinateBranchMatrixUnit
          m w z q stage hstage port left right := by
  rw [decodedRetryPoolSuccessorCoordinateBranchChannel,
    QuantumChannel.comp_apply,
    decodedRetryPoolSuccessorCoordinateTensorChannel_rankOne_basis]
  rw [map_smul]
  exact congrArg
    (fun A => decodedRetryPoolSuccessorCoordinateBranchCoefficient
      m w z q stage port left right • A)
    (decodedRetryPoolSuccessorCoordinateBranchRouteChannel_rankOne_basis
      m w z q stage hstage port left right)
end QEC.Distillation.HH18Parameterized
