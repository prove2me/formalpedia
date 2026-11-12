-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_terminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:01:29.508581+00:00
-- url     : https://prove2.me/submissions/83ef7479-d7cc-487c-b5b3-3c55c5db919e

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_DyadicSlack
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule

set_option autoImplicit false
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding
open Coding.ReedMuller Coding.PuncturedReedMuller
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution (m w z q : Nat) (hz : 0 < z) :
    decodedRetryPoolBackwardSchedule m w z q ⟨z - 1, by omega⟩ = q := by
  change decodedRetryPoolBackwardRequiredAtDistance m w z q (z - 1 - (z - 1)) = q
  rw [Nat.sub_self]
  rfl
end QEC.Distillation.HH18Parameterized
