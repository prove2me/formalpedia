-- Prove2me | solution 1 for QEC.Distillation.HH18Parameterized.decodedRetryPoolSuccessorRegroupChannel_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T19:35:22.977268+00:00
-- url     : https://prove2.me/submissions/153f0759-769d-4498-b719-e4c7d0f5b2f5

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
      (decodedRetryPoolSuccessorTargetSlots m w z q stage hstage))) :
    decodedRetryPoolSuccessorRegroupChannel m w z q stage hstage A =
      (decodedRetryPoolSuccessorRegroupTransport m w z q stage hstage).conjOperator A :=
  rfl
end QEC.Distillation.HH18Parameterized
