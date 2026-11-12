-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:00:43.153412+00:00
-- url     : https://prove2.me/submissions/3fddfc36-0fb4-4248-99b2-47ffc4461473

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
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    ∃ coordinate : decodedRetryPoolPhysicalExactBatchOutputSlots m w depth,
      decodedRetryPoolPhysicalExactBatchActualOutputError
          h hdegree epsilon depth rhoUnit =
        decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
          (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
          (Nat.succ_pos depth) coordinate
          (decodedRetryPoolPhysicalExactBatchRun
            h hdegree epsilon depth rhoUnit).acceptedOutput := by
  classical
  unfold decodedRetryPoolPhysicalExactBatchActualOutputError
  obtain ⟨coordinate, _, hcoordinate⟩ := Finset.exists_mem_eq_sup'
    ⟨(decodedRetryPoolPhysicalExactBatchOutputSlots_nonempty
      m w depth).some, Finset.mem_univ _⟩
    (fun coordinate =>
      decodedRetryPoolPhysicalProtocolCoordinateRawError m w (depth + 1)
        (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
        (Nat.succ_pos depth) coordinate
        (decodedRetryPoolPhysicalExactBatchRun
          h hdegree epsilon depth rhoUnit).acceptedOutput)
  exact ⟨coordinate, hcoordinate⟩
end QEC.Distillation.HH18Parameterized
