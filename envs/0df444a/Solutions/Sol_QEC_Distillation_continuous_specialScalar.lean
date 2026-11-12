-- Prove2me | solution 1 for QEC.Distillation.continuous_specialScalar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:15:52.772538+00:00
-- url     : https://prove2.me/submissions/a705d1ad-95e9-484c-969e-5dddde235184

import Definitions.Def_QEC_Distillation_Universality_SU2AxisCircle
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.LinearAlgebra.CrossProduct
import Definitions.Def_QEC_Distillation_Universality_SU2NonparallelAxes

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open Matrix
namespace QEC.Distillation
theorem _root_.solution : Continuous specialScalar := by
  unfold specialScalar
  have hgate : Continuous (fun U : SingleQubitGate => (U : SingleQubitMatrix)) :=
    continuous_induced_dom
  exact Complex.continuous_re.comp
    ((continuous_apply 0).comp ((continuous_apply 0).comp
      (hgate.comp continuous_subtype_val)))
end QEC.Distillation
