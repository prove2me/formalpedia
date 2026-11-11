-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:02:52.281723+00:00
-- url     : https://prove2.me/submissions/69eefc06-d719-4181-9160-c1d4aad8dd54

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
    phaseShiftLinearEquiv theta psi = phaseShiftOperator theta psi :=
  rfl
end QEC.Distillation.OneQubitMagic
