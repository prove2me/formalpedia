-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15Run_successProbability_closed_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:56:50.889361+00:00
-- url     : https://prove2.me/submissions/07e6f28b-a256-4f58-a294-3e1a40445852

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_endpointWeight_eq_closedForm
import Theorems.Thm_QEC_Distillation_BK15_Protocol_bk15Run_successProbability
attribute [local simp] QEC.Distillation.BK15.Protocol.bk15Run_successProbability



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Recurrence
open Semantics Semantics.Qubit
open Coding.PauliSymplectic
open NoisyInput Protocol
open scoped BigOperators TensorProduct
namespace QEC.Distillation.BK15.Recurrence
theorem _root_.solution
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    (bk15Run epsilon hpositive).successProbability =
      (1 + 15 * bk15_r epsilon ^ 8) / 16 := by
  rw [bk15Run_successProbability, accepted_endpointWeight_eq_closedForm]
end QEC.Distillation.BK15.Recurrence
