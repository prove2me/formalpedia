-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseShiftGate_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:47:26.397951+00:00
-- url     : https://prove2.me/submissions/20cc37c9-4226-47e2-83fc-d72616313963

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution (theta : Real) :
    (phaseShiftGate theta : Matrix (Fin 2) (Fin 2) Complex) = phaseShiftMatrix theta :=
  rfl
end QEC.Distillation.OneQubitMagic
