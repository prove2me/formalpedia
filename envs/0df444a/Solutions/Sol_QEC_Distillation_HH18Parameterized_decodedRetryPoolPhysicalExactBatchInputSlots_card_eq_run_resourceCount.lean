-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchInputSlots_card_eq_run_resourceCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:21:58.317476+00:00
-- url     : https://prove2.me/submissions/bf116935-e28b-42ab-8cef-a28249548ed4

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRootInputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolRun_resourceCount
attribute [local simp] QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalProtocolRun_resourceCount



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    {w r m : Nat} (h : Admissible w r m) (hdegree : 3 * r < m)
    (epsilon : HH18NoisyInput.DiagonalErrorRate) (depth : Nat)
    (rhoUnit : DensityOperator
      (tensorPowerCarrier (PhysicalRegister m w) 0)) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchInputSlots m w depth) =
      (decodedRetryPoolPhysicalExactBatchRun
        h hdegree epsilon depth rhoUnit).resourceCount := by
  rw [decodedRetryPoolPhysicalProtocolRootInputSlots_card,
    decodedRetryPoolPhysicalProtocolRun_resourceCount]
end QEC.Distillation.HH18Parameterized
