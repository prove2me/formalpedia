-- Prove2me | solution 1 for QEC.Distillation.axisCircle_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:09:31.234003+00:00
-- url     : https://prove2.me/submissions/0098b69d-63bd-4690-a413-dc2aff099bc3

import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.Polynomial.Basic
import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open GeneratedUniversality
namespace QEC.Distillation
theorem _root_.solution (axis : UnitBlochAxis) (t u : AddCircle (2 * Real.pi)) :
    axisCircle axis (t + u) = axisCircle axis t * axisCircle axis u := by
  apply Subtype.ext
  change axisCircleMatrix axis (AddCircle.toCircle (t + u)) =
    axisCircleMatrix axis (AddCircle.toCircle t) * axisCircleMatrix axis (AddCircle.toCircle u)
  rw [AddCircle.toCircle_add]
  exact (axisCircleMatrix_mul axis _ _).symm
end QEC.Distillation
