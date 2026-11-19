-- Prove2me | solution 1 for QEC.Distillation.BK15.Recurrence.bk15_recurrence_scaled_denominator_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:24:59.841943+00:00
-- url     : https://prove2.me/submissions/c1664a4e-6311-4139-ad53-74052d1f22ec

import Definitions.Def_QEC_Distillation_FifteenQubitH_Protocol
import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_recurrence_denominator_pos

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
theorem _root_.solution (epsilon : BK15Epsilon) :
    0 < 2 * (1 + 15 * bk15_r epsilon ^ 8) := by
  nlinarith [bk15_recurrence_denominator_pos epsilon]
end QEC.Distillation.BK15.Recurrence
