-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.hadamardGate_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:52:40.6533+00:00
-- url     : https://prove2.me/submissions/ccacc391-4866-4dc0-9fe0-bba796a69e62

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
    Matrix.toEuclideanLin (hadamardGate : Matrix (Fin 2) (Fin 2) Complex) psi =
      hadamardTransport psi :=
  rfl
end QEC.Distillation.OneQubitMagic
