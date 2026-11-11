-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseGate_apply_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:55:02.978566+00:00
-- url     : https://prove2.me/submissions/7270288a-96e2-4641-8928-212c1b766cbd

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
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi 0 = psi 0 := by
  rw [phaseGate_apply]
  exact phaseOperator_apply_zero psi
end QEC.Distillation.OneQubitMagic
