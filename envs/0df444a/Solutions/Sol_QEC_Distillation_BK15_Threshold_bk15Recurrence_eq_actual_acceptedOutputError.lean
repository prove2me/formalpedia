-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15Recurrence_eq_actual_acceptedOutputError
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:29:33.639461+00:00
-- url     : https://prove2.me/submissions/54c4fb74-e2b1-41bd-95a9-f08e9f4d0831

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Recurrence_bk15_acceptedOutputError_closed_form


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
theorem _root_.solution
    (epsilon : BK15Epsilon) (hpositive : 0 < epsilon.epsilon) :
    bk15Recurrence epsilon.epsilon =
      bk15OutputError (bk15Run epsilon hpositive).acceptedOutput aZeroDensity := by
  rw [bk15_acceptedOutputError_closed_form epsilon hpositive]
  rfl
end QEC.Distillation.BK15.Threshold
