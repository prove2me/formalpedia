-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolPhysicalExactBatchOutputSlots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:36:50.054948+00:00
-- url     : https://prove2.me/submissions/134b66fa-9321-432a-b5be-c8334c513f6d

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_AcceptedError
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_Cost
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolOutputCoordinate_card


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
    (m w depth : Nat) :
    Fintype.card (decodedRetryPoolPhysicalExactBatchOutputSlots m w depth) =
      decodedRetryPoolExactBatchTerminalRequest (depth + 1) *
        logicalOutputCount m w ^ (depth + 1) :=
  decodedRetryPoolPhysicalProtocolOutputCoordinate_card m w (depth + 1)
    (decodedRetryPoolExactBatchTerminalRequest (depth + 1))
    (Nat.succ_pos depth)
end QEC.Distillation.HH18Parameterized
