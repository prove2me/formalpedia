-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseInverseGate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:16:50.539962+00:00
-- url     : https://prove2.me/submissions/56f8ca57-3c20-410b-9acb-0d503a06262c

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (psi : QubitSpace) :
    Matrix.toEuclideanLin (phaseInverseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseInverseOperator psi :=
  rfl
end QEC.Distillation.OneQubitMagic
