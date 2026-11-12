-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchActualOutputError_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T23:06:09.548578+00:00
-- url     : https://prove2.me/submissions/795a0438-f323-44fb-b5e9-568b2c306e1e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Asymptotic
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg


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
    0 <= decodedRetryPoolPhysicalExactBatchActualOutputError
      h hdegree epsilon depth rhoUnit := by
  obtain ⟨coordinate, hcoordinate⟩ :=
    decodedRetryPoolPhysicalExactBatchActualOutputError_exists_coordinate
      h hdegree epsilon depth rhoUnit
  rw [hcoordinate]
  exact decodedRetryPoolPhysicalProtocolCoordinateRawError_nonneg
    m w (depth + 1)
      (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
      (Nat.succ_pos depth) coordinate _
end QEC.Distillation.HH18Parameterized
