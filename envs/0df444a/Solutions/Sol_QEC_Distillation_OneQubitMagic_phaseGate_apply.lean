-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseGate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:52:54.602063+00:00
-- url     : https://prove2.me/submissions/d782eb5e-f9a8-4f6f-b544-6f2a763b6557

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
    Matrix.toEuclideanLin (phaseGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      phaseTransport psi :=
  rfl
end QEC.Distillation.OneQubitMagic
