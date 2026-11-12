-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTSin_mul_sourceTCos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:58:49.357089+00:00
-- url     : https://prove2.me/submissions/bbe7b441-fa3f-49f9-9f5e-793061172a18

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.OneQubitMagic
open Semantics Semantics.Qubit
open TwoQubit
open scoped InnerProductSpace TensorProduct
namespace QEC.Distillation.OneQubitMagic
theorem _root_.solution :
    sourceTSin * sourceTCos = sourceTParameter / Real.sqrt 2 := by
  unfold sourceTSin
  field_simp [sourceTCos_ne_zero, sqrt_two_pos.ne']
end QEC.Distillation.OneQubitMagic
