-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolBackwardSchedule_preterminal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:43:23.215607+00:00
-- url     : https://prove2.me/submissions/93539da6-4d4e-4022-899f-68cc44989754

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
theorem _root_.solution (m w z q : Nat) (hdepth : z = 2) :
    decodedRetryPoolBackwardSchedule m w z q ⟨0, by omega⟩ =
      physicalInputCount m w * decodedRetryPoolDyadicAttempts 1 q := by
  subst z
  change decodedRetryPoolBackwardRequiredAtDistance m w 2 q 1 =
    physicalInputCount m w * decodedRetryPoolDyadicAttempts 1 q
  rfl
end QEC.Distillation.HH18Parameterized
