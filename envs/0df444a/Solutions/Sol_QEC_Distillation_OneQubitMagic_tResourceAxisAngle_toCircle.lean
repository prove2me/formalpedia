-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.tResourceAxisAngle_toCircle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:21:06.5372+00:00
-- url     : https://prove2.me/submissions/279de180-74ca-4b9a-9e45-3c0e0b456fce

import Definitions.Def_QEC_Distillation_Universality_SU2GeneratedDensity
import Mathlib.NumberTheory.Niven
import Definitions.Def_QEC_Distillation_Universality_TPhaseGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisAngle_cos
import Theorems.Thm_QEC_Distillation_OneQubitMagic_tResourceAxisAngle_sin

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    (AddCircle.toCircle
        (tResourceAxisAngle : AddCircle (2 * Real.pi)) : Complex) =
      (3 / 4 : Complex) + (Real.sqrt 7 / 4 : Complex) * Complex.I := by
  rw [AddCircle.toCircle_apply_mk]
  have hscale : (2 * Real.pi) / (2 * Real.pi) = (1 : Real) := by
    exact div_self (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  rw [hscale, one_mul, Circle.coe_exp, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    tResourceAxisAngle_cos, tResourceAxisAngle_sin]
  push_cast
  ring
end QEC.Distillation.OneQubitMagic
