-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_pi_div_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:24:38.278212+00:00
-- url     : https://prove2.me/submissions/ab20b166-b177-4049-a1f1-587bf1d0ed7a

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    phaseAmplitude (Real.pi / 4) =
      (Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((Real.pi / 4 : Real) : Complex) * Complex.I) =
        (Real.cos (Real.pi / 4) : Complex) +
          (Real.sin (Real.pi / 4) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (Real.pi / 4)
    _ = (Real.sqrt 2 / 2 : Complex) +
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
      rw [Real.cos_pi_div_four, Real.sin_pi_div_four]
      push_cast
      ring
end QEC.Distillation.OneQubitMagic
