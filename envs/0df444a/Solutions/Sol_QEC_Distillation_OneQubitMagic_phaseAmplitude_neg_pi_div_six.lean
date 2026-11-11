-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_neg_pi_div_six
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:10:51.421574+00:00
-- url     : https://prove2.me/submissions/0c5bb406-aa52-4f3f-80e8-76e8493444fa

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
    phaseAmplitude (-Real.pi / 6) =
      (Real.sqrt 3 / 2 : Complex) - (2 : Complex)⁻¹ * Complex.I := by
  unfold phaseAmplitude
  calc
    Complex.exp (((-Real.pi / 6 : Real) : Complex) * Complex.I) =
        (Real.cos (-Real.pi / 6) : Complex) +
          (Real.sin (-Real.pi / 6) : Complex) * Complex.I :=
      Complex.exp_ofReal_mul_I (-Real.pi / 6)
    _ = (Real.sqrt 3 / 2 : Complex) - (2 : Complex)⁻¹ * Complex.I := by
      rw [show -Real.pi / 6 = -(Real.pi / 6) by ring,
        Real.cos_neg, Real.sin_neg, Real.cos_pi_div_six,
        Real.sin_pi_div_six]
      push_cast
      norm_num
      ring
end QEC.Distillation.OneQubitMagic
