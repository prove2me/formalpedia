-- Prove2me | solution 1 for QEC.Distillation.phaseNormalize_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T14:10:38.72083+00:00
-- url     : https://prove2.me/submissions/b28c6fc2-5e20-4c07-87e9-4759bd969516

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
theorem _root_.solution (U : SingleQubitGate) :
    (phaseNormalize U : SingleQubitMatrix) = (determinantRoot U)⁻¹ • (U : SingleQubitMatrix) :=
  rfl
end QEC.Distillation
