-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorOneQubitRecordChannel_selectedOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:44:04.14094+00:00
-- url     : https://prove2.me/submissions/d0a88ec3-110d-4795-a70b-8c55a2ce87c5

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Preparation
import Definitions.Def_QEC_Semantics_Instruments_Registers_ChannelProduct
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity
import Theorems.Thm_QEC_Distillation_EncodedCode_ImplementsLogicalGate_symm
import Theorems.Thm_QEC_Distillation_HH18Parameterized_selectedLogicalPortDephasedOutput_eq_diagonalAResource


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
open Triorthogonal.BH12NoisyInjection
open Triorthogonal.BH12NoisyInjection.OneQubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (port : LogicalSite m w) :
    decodedRetryPoolSuccessorOneQubitRecordChannel.mapDensity
        (selectedLogicalPortTransportedAcceptedOutput h hdegree epsilon port) =
      decodedRetryPoolOneQubitRecordDensity
        (selectedLogicalPortRawParameter h hdegree epsilon port) := by
  rw [decodedRetryPoolSuccessorOneQubitRecordChannel_mapDensity]
  change aBasisTransport.symm.conjDensity
      (selectedLogicalPortDephasedOutput h hdegree epsilon port) = _
  rw [selectedLogicalPortDephasedOutput_eq_diagonalAResource]
  rfl
end QEC.Distillation.HH18Parameterized
