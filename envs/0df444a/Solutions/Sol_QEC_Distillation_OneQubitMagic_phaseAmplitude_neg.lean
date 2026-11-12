-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T04:19:33.943568+00:00
-- url     : https://prove2.me/submissions/3a3ca563-573c-4b84-9327-18de8b275fb6

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
theorem _root_.solution (theta : Real) :
    phaseAmplitude (-theta) = (phaseAmplitude theta)⁻¹ := by
  unfold phaseAmplitude
  rw [show (((-theta : Real) : Complex) * Complex.I) =
      -((theta : Complex) * Complex.I) by
    push_cast
    ring]
  exact Complex.exp_neg _
end QEC.Distillation.OneQubitMagic
