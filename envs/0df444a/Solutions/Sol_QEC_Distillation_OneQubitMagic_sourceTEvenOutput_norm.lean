-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTEvenOutput_norm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:59:23.015538+00:00
-- url     : https://prove2.me/submissions/16bc6d6c-14e7-420b-b7b1-dc0af0915cf7

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
theorem _root_.solution : ‖hadamardOperator sourceTEvenFirstQubit‖ = 1 := by
  change ‖hadamardTransport.toLinearIsometryEquiv sourceTEvenFirstQubit‖ = 1
  rw [hadamardTransport.toLinearIsometryEquiv.norm_map]
  exact zzEvenBranchFirstQubit_norm sourceTTwoQubitState sourceTEvenWeight_pos
end QEC.Distillation.OneQubitMagic
