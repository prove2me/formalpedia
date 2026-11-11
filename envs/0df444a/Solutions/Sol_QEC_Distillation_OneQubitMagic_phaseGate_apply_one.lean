-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseGate_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:55:06.002253+00:00
-- url     : https://prove2.me/submissions/c75a3f84-14d3-4889-8577-494a10efc63f

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_phaseGate_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      Complex.I * psi 1 := by
  rw [phaseGate_apply]
  exact phaseOperator_apply_one psi
end QEC.Distillation.OneQubitMagic
