-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:02:58.154544+00:00
-- url     : https://prove2.me/submissions/71d6e849-7a5e-4318-8d6d-64a7a9526726

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
theorem _root_.solution (theta : Real) (psi : QubitSpace) :
    phaseShiftTransport theta psi = phaseShiftOperator theta psi :=
  rfl
end QEC.Distillation.OneQubitMagic
