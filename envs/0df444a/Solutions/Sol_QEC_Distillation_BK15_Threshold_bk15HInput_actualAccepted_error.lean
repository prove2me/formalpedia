-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15HInput_actualAccepted_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T21:32:20.445851+00:00
-- url     : https://prove2.me/submissions/9274fce7-605d-412f-a390-51959890fc6e

import Definitions.Def_QEC_Distillation_FifteenQubitH_Recurrence
import Definitions.Def_QEC_Distillation_FifteenQubitH_Threshold
import Theorems.Thm_QEC_Distillation_BK15_Threshold_bk15Recurrence_eq_actual_acceptedOutputError

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
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    bk15Recurrence (bk15HInputError rho) =
      bk15OutputError
        (bk15Run (bk15HInputEpsilon rho hpositive hleHalf)
          (bk15HInputEpsilon_pos rho hpositive hleHalf)).acceptedOutput
        aZeroDensity := by
  exact bk15Recurrence_eq_actual_acceptedOutputError
      (bk15HInputEpsilon rho hpositive hleHalf)
      (bk15HInputEpsilon_pos rho hpositive hleHalf)
end QEC.Distillation.BK15.Threshold
