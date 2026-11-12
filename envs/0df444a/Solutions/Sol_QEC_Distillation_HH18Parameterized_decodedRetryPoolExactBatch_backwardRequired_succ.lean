-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolExactBatch_backwardRequired_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T20:58:56.851362+00:00
-- url     : https://prove2.me/submissions/f1fe243f-682d-4e65-9cc0-b22ca79e081a

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Physical_ScheduleBridge
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_ExactBatching
import Theorems.Thm_QEC_Distillation_HH18Parameterized_decodedRetryPoolDyadicAttempts_slack_multiple

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z multiple distance : Nat) :
    decodedRetryPoolBackwardRequiredAtDistance m w (z + 1)
        (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1))
        (distance + 1) =
      decodedRetryPoolBackwardRequiredAtDistance m w z
        ((physicalInputCount m w * decodedRetryPoolDyadicDenominator z * multiple) *
          decodedRetryPoolExactBatchTerminalRequest z)
        distance := by
  induction distance with
  | zero =>
      change physicalInputCount m w *
          decodedRetryPoolDyadicAttempts z
            (multiple * decodedRetryPoolExactBatchTerminalRequest (z + 1)) =
        (physicalInputCount m w * decodedRetryPoolDyadicDenominator z * multiple) *
          decodedRetryPoolExactBatchTerminalRequest z
      rw [decodedRetryPoolExactBatchTerminalRequest]
      have hrequest :
          multiple *
              ((decodedRetryPoolDyadicDenominator z - 1) *
                decodedRetryPoolExactBatchTerminalRequest z) =
            (decodedRetryPoolDyadicDenominator z - 1) *
              (multiple * decodedRetryPoolExactBatchTerminalRequest z) := by
        ring
      rw [hrequest, decodedRetryPoolDyadicAttempts_slack_multiple]
      ring
  | succ distance ih =>
      conv_lhs => rw [decodedRetryPoolBackwardRequiredAtDistance]
      conv_rhs => rw [decodedRetryPoolBackwardRequiredAtDistance]
      have hstage :
          z + 1 - (distance + 1 + 1) = z - (distance + 1) := by
        omega
      rw [hstage, ih]
end QEC.Distillation.HH18Parameterized
