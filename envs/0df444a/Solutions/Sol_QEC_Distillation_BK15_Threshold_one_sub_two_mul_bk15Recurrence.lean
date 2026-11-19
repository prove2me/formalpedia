-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.one_sub_two_mul_bk15Recurrence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:28:05.560077+00:00
-- url     : https://prove2.me/submissions/990a5403-04e6-45bc-bc33-b3d6ad337986

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.BK15
open QEC.Distillation.BK15.Threshold
open Semantics Semantics.Qubit
open NoisyInput Protocol Recurrence
open OneQubitMagic
namespace QEC.Distillation.BK15.Threshold
theorem _root_.solution (epsilon : Real) :
    1 - 2 * bk15Recurrence epsilon =
      bk15Bias epsilon ^ 7 * (15 + bk15Bias epsilon ^ 8) /
        (1 + 15 * bk15Bias epsilon ^ 8) := by
  have hdenom : 1 + 15 * bk15Bias epsilon ^ 8 ≠ 0 :=
    (bk15Recurrence_denominator_pos epsilon).ne'
  unfold bk15Recurrence
  field_simp [hdenom]
  ring
end QEC.Distillation.BK15.Threshold
