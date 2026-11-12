-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorReindexChannel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:14:53.945822+00:00
-- url     : https://prove2.me/submissions/dad47f7e-7911-4518-8daa-87f01264cd62

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
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorReindexChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegisterTransport m w z q stage hstage).conjOperator A :=
  rfl
end QEC.Distillation.HH18Parameterized
