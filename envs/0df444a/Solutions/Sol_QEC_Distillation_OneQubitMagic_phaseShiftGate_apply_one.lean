-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftGate_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:54:44.910652+00:00
-- url     : https://prove2.me/submissions/5414ddf3-0ce1-4cde-9854-dea2122dc3d5

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
    Matrix.toEuclideanLin (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      phaseAmplitude theta * psi 1 := by
  rw [phaseShiftGate_apply]
  exact phaseShiftOperator_apply_one theta psi
end QEC.Distillation.OneQubitMagic
