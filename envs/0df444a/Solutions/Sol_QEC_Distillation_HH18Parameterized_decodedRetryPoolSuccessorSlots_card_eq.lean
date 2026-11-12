-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorSlots_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:44:50.007616+00:00
-- url     : https://prove2.me/submissions/8af42982-7e54-4682-a66d-d15c652c2654

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Schedule_BackwardSchedule
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Routing

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z) :
    Fintype.card (decodedRetryPoolSuccessorSourceSlots m w z q stage) =
      Fintype.card (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage) :=
  Fintype.card_congr (decodedRetryPoolSuccessorSlotEquiv m w z q stage hstage)
end QEC.Distillation.HH18Parameterized
