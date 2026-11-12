-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_pi_div_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:00:05.43193+00:00
-- url     : https://prove2.me/submissions/22bd90ec-bc8b-4069-8197-1e27a4a14b49

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
    phaseAmplitude (Real.pi / 8) =
      (Real.cos (Real.pi / 8) : Complex) +
        (Real.sin (Real.pi / 8) : Complex) * Complex.I := by
  unfold phaseAmplitude
  exact Complex.exp_ofReal_mul_I (Real.pi / 8)
end QEC.Distillation.OneQubitMagic
