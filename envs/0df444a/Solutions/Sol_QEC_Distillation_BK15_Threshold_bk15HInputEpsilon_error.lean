-- Prove2me | solution 1 for QEC.Distillation.BK15.Threshold.bk15HInputEpsilon_error
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T04:31:46.265448+00:00
-- url     : https://prove2.me/submissions/1e4210f8-3790-4ffe-a34b-a9cdfd3d08eb

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
theorem _root_.solution
    (rho : DensityOperator QubitSpace)
    (hpositive : 0 < bk15HInputError rho)
    (hleHalf : bk15HInputError rho <= 1 / 2) :
    (bk15HInputEpsilon rho hpositive hleHalf).epsilon = bk15HInputError rho :=
  rfl
end QEC.Distillation.BK15.Threshold
