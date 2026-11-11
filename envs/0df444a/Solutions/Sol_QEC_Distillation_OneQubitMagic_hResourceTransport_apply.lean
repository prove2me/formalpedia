-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hResourceTransport_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:11:25.613787+00:00
-- url     : https://prove2.me/submissions/5efa7de4-ab76-44f6-9203-18269befd8c4

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
theorem _root_.solution (psi : QubitSpace) :
    hResourceTransport psi = hadamardOperator (phaseOperator psi) :=
  rfl
end QEC.Distillation.OneQubitMagic
