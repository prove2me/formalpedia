-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorNestedInputChannel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:35:45.663176+00:00
-- url     : https://prove2.me/submissions/b7fec1b5-a28e-4909-8a79-7ff36ae8d2ab

import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Measurement
import Definitions.Def_QEC_Distillation_LowOverheadProtocol_Parameterized_RetryPool_Successor_Regrouping

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.HH18Parameterized
open Coding Semantics
open Coding.ReedMuller Coding.PuncturedReedMuller
open Semantics.Qubit
open Semantics.FiniteInstrument
attribute [local instance 100] Fintype.ofFinite
namespace QEC.Distillation.HH18Parameterized
theorem _root_.solution
    (m w z q : Nat) (stage : Fin z) (hstage : stage.1 + 1 < z)
    (A : Operator (Qubit.QubitRegister
      (decodedRetryPoolSuccessorSourceSlots m w z q stage))) :
    decodedRetryPoolSuccessorNestedInputChannel m w z q stage hstage A =
      decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage
        (decodedRetryPoolSuccessorReindexChannel m w z q stage hstage
          (decodedRetryPoolSuccessorRecordPreparationChannel m w z q stage A)) :=
  rfl
end QEC.Distillation.HH18Parameterized
