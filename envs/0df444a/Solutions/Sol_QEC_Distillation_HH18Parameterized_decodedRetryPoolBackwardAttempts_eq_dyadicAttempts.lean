-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardAttempts_eq_dyadicAttempts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:43:39.137212+00:00
-- url     : https://prove2.me/submissions/820eb73a-d0ab-4384-9b49-bcc06872e66a

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
theorem _root_.solution
    (m w z q : Nat) (stage : Fin z) :
    decodedRetryPoolBackwardAttempts m w z q stage =
      decodedRetryPoolDyadicAttempts stage.1
        (decodedRetryPoolBackwardSchedule m w z q stage) := rfl
end QEC.Distillation.HH18Parameterized
