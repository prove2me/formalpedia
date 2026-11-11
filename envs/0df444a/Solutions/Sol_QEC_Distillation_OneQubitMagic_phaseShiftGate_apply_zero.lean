-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:54:41.735179+00:00
-- url     : https://prove2.me/submissions/5495e0ed-be65-4548-85d6-2e8be51878d2

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseShiftGate_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (theta : Real) (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 0 =
      psi 0 := by
  rw [phaseShiftGate_apply]
  exact phaseShiftOperator_apply_zero theta psi
end QEC.Distillation.OneQubitMagic
