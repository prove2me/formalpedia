-- Prove2me | solution 1 for QEC.Distillation.axisCircle_axis_recovery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:17:59.183263+00:00
-- url     : https://prove2.me/submissions/ec439ab3-d7ed-40b4-abbe-e652fa607e89

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Theorems.Thm_QEC_Distillation_axisCircleMatrix_axis_recovery

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution {axis axis' : UnitBlochAxis}
    (t : AddCircle (2 * Real.pi))
    (h_im : (AddCircle.toCircle t : Complex).im ≠ 0)
    (hgate : axisCircle axis t = axisCircle axis' t) : axis = axis' := by
  apply axisCircleMatrix_axis_recovery h_im
  exact congrArg (fun U : SingleQubitGate => (U : SingleQubitMatrix)) hgate
end QEC.Distillation
