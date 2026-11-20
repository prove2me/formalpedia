-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.zeroEpsilon_accepted_endpointWeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T12:56:54.179212+00:00
-- url     : https://prove2.me/submissions/1330cdb5-ad53-409d-a725-cb10a68bbae4

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_accepted_endpointWeight_eq_closedForm

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
theorem _root_.solution :
    endpointWeight zeroEpsilon .accepted = 1 := by
  rw [accepted_endpointWeight_eq_closedForm]
  norm_num [bk15_r, zeroEpsilon]
end QEC.Distillation.BK15.Recurrence
