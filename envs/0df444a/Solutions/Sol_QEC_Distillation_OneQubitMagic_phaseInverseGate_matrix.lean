-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.phaseInverseGate_matrix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T13:47:23.285308+00:00
-- url     : https://prove2.me/submissions/6f185cd0-8fb1-49cc-9f36-fa639b2189db

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Universality_GeneratedUniversality
import Definitions.Def_QEC_Distillation_Universality_OneQubitGeneratedUniversality

set_option autoImplicit false
noncomputable section
open QEC QEC.Distillation QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open GeneratedUniversality
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    (phaseInverseGate : Matrix (Fin 2) (Fin 2) Complex) = phaseInverseMatrix :=
  rfl
end QEC.Distillation.OneQubitMagic
