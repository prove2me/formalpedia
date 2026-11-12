-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRootInputTransport_apply_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:07:14.662112+00:00
-- url     : https://prove2.me/submissions/bfddd620-d27f-44a8-a79e-7510a9906e83

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Protocol
import Definitions.Def_QEC_Semantics_Instruments_NestedTensor_PowerBasis
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Accounting
import Theorems.Thm_QEC_Semantics_FiniteInstrument_tensorPowerQubitRegisterTransport_apply_basis
attribute [local simp] QEC.Semantics.FiniteInstrument.tensorPowerQubitRegisterTransport_apply_basis



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
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q : Nat) (hz : 0 < z)
    (history : tensorPowerHistory (Qubit.Bitstring (PhysicalSite m w))
      (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩)) :
    decodedRetryPoolPhysicalProtocolRootInputTransport m w z q hz
      (tensorPowerBasis
        (EuclideanSpace.basisFun (Qubit.Bitstring (PhysicalSite m w)) Complex)
        (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) =
      EuclideanSpace.basisFun
        (Qubit.Bitstring (decodedRetryPoolBackwardRootRawCarrier m w z q hz)) Complex
        (tensorPowerQubitBitstringEquiv (PhysicalSite m w)
          (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history) := by
  exact tensorPowerQubitRegisterTransport_apply_basis
    (PhysicalSite m w)
    (decodedRetryPoolBackwardAttempts m w z q ⟨0, hz⟩) history
end QEC.Distillation.HH18Parameterized
