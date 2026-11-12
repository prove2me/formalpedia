-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_neg_pi_div_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:59:20.359462+00:00
-- url     : https://prove2.me/submissions/84ea28e0-d78e-44be-bd9d-a2e1532c47d6

import Definitions.Def_QEC_Distillation_Universality_OneQubitClifford
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_Universality_OneQubitPhase

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    phaseAmplitude (-Real.pi / 4) =
      (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 4 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 4) : Complex) +
          (Real.sin (-Real.pi / 4) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 4)
    _ = (Real.sqrt 2 / 2 : Complex) -
        (Real.sqrt 2 / 2 : Complex) * Complex.I := by
      rw [show -Real.pi / 4 = -(Real.pi / 4) by ring,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_four,
        Real.sin_pi_div_four]
      push_cast
      ring
end QEC.Distillation.OneQubitMagic
