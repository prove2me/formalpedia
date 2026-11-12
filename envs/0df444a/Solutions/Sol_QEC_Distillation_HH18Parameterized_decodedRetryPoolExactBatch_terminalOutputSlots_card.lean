-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_terminalOutputSlots_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:58:03.795396+00:00
-- url     : https://prove2.me/submissions/003fc0ff-8bef-4bf3-9beb-9061cad01972

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card


set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z : Nat) :
    Fintype.card
        (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w z
          (decodedRetryPoolExactBatchTerminalRequest z)) =
      decodedRetryPoolExactBatchTerminalRequest z *
        logicalOutputCount m w ^ z :=
  decodedRetryPoolPhysicalProtocolTerminalOutputSlots_card m w z
    (decodedRetryPoolExactBatchTerminalRequest z)
end QEC.Distillation.HH18Parameterized
