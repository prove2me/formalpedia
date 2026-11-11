-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftLinearEquiv_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T12:02:55.220451+00:00
-- url     : https://prove2.me/submissions/90ac28c5-2817-44d3-8b76-a74adfb5100f

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
theorem _root_.solution
    (theta : Real) (psi : QubitSpace) :
    (phaseShiftLinearEquiv theta).symm psi =
      phaseShiftOperator (-theta) psi :=
  rfl
end QEC.Distillation.OneQubitMagic
