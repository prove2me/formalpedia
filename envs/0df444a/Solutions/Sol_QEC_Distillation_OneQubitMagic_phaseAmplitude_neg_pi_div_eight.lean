-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_neg_pi_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:00:51.168197+00:00
-- url     : https://prove2.me/submissions/638674a1-bed0-4f26-ab5a-530461534fe4

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Semantics_ErrorCorrection_QuditSubsystem
import Definitions.Def_QEC_Distillation_Universality_HResourcePhase

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    phaseAmplitude (-Real.pi / 8) =
      (Real.cos (Real.pi / 8) : Complex) -
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 8 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 8) : Complex) +
          (Real.sin (-Real.pi / 8) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 8)
    _ = (Real.cos (Real.pi / 8) : Complex) -
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
      rw [show -Real.pi / 8 = -(Real.pi / 8) by ring,
        Real.cos_neg, Real.sin_neg]
      push_cast
      ring
end QEC.Distillation.OneQubitMagic
