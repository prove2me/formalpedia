-- Prove2me | solution 1 for QEC.Distillation.continuous_specialVector
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:16:06.067785+00:00
-- url     : https://prove2.me/submissions/ac76f1bc-649b-498a-ae8b-e44fcbfef6a8

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
theorem _root_.solution : Continuous specialVector := by
  have hgate : Continuous (fun U : SingleQubitGate => (U : SingleQubitMatrix)) :=
    continuous_induced_dom
  have hmatrix : Continuous (fun U : SingleQubitSpecialUnitary =>
      (U : SingleQubitMatrix)) :=
    hgate.comp continuous_subtype_val
  rw [continuous_pi_iff]
  intro i
  fin_cases i
  · exact (Complex.continuous_im.comp
      ((continuous_apply 1).comp ((continuous_apply 0).comp hmatrix))).neg
  · exact (Complex.continuous_re.comp
      ((continuous_apply 1).comp ((continuous_apply 0).comp hmatrix))).neg
  · exact (Complex.continuous_im.comp
      ((continuous_apply 0).comp ((continuous_apply 0).comp hmatrix))).neg
end QEC.Distillation
