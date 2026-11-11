-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseAmplitude_two_pi_mul_int
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:32:19.111349+00:00
-- url     : https://prove2.me/submissions/958f8bd0-0e26-4e2f-8ea9-61cb5c751a13

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
theorem _root_.solution (k : Int) :
    phaseAmplitude ((2 * Real.pi) * (k : Real)) = 1 := by
  unfold phaseAmplitude
  convert Complex.exp_int_mul_two_pi_mul_I k using 1
  all_goals push_cast
  all_goals ring_nf
end QEC.Distillation.OneQubitMagic
