-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamardGate_apply_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:54:21.86414+00:00
-- url     : https://prove2.me/submissions/5630ee0e-b53a-466c-ba6f-8f09605484d7

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality
import Theorems.Thm_QEC_Distillation_OneQubitMagic_hadamardGate_apply

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (psi : QubitSpace) :
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi 1 =
      (Real.sqrt 2 : Complex)⁻¹ * (psi 0 - psi 1) := by
  rw [hadamardGate_apply]
  exact hadamardOperator_apply_one psi
end QEC.Distillation.OneQubitMagic
