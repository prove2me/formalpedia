-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_physicalCost_four_thirds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T21:15:24.943684+00:00
-- url     : https://prove2.me/submissions/f126c3ed-31b7-4a38-bad3-8c086f2fb61e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_rootInputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_terminalOutputSlots_card
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolExactBatch_retryFactor_four_thirds

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z : Nat) :
    3 * logicalOutputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolRootInputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1)) (Nat.succ_pos z)) ≤
      4 * physicalInputCount m w ^ (z + 1) *
        Fintype.card
          (decodedRetryPoolPhysicalProtocolTerminalOutputSlots m w (z + 1)
            (decodedRetryPoolExactBatchTerminalRequest (z + 1))) := by
  rw [decodedRetryPoolExactBatch_rootInputSlots_card,
    decodedRetryPoolExactBatch_terminalOutputSlots_card]
  have hfactor := decodedRetryPoolExactBatch_retryFactor_four_thirds (z + 1)
  have hscaled := Nat.mul_le_mul_left
    (physicalInputCount m w ^ (z + 1) * logicalOutputCount m w ^ (z + 1)) hfactor
  convert hscaled using 1 <;> ring
end QEC.Distillation.HH18Parameterized
