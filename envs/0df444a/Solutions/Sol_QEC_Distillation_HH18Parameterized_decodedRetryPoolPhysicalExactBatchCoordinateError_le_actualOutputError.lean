-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchCoordinateError_le_actualOutputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:07:31.511102+00:00
-- url     : https://prove2.me/submissions/28fd1d18-a4aa-45d2-a9de-310203e0c705

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic

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
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0))
    (coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) :
    decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput <=
      decodedRetryPoolPhysicalExactBatchActualOutputError
        h hdegree epsilon depth rhoUnit := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  exact Finset.le_sup'
    (fun other : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) other
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput)
    (Finset.mem_univ coordinate)
end QEC.Distillation.HH18Parameterized
