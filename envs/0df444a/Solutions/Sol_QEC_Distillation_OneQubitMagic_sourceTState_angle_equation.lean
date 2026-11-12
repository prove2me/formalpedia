-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTState_angle_equation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:22:19.574938+00:00
-- url     : https://prove2.me/submissions/c1fcba34-cc88-4d6b-a1d5-634e4eb978b7

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
    sourceTCos ^ 2 - sourceTSin ^ 2 = sourceTParameter := by
  rw [sourceTCos_sq, sourceTSin_sq]
  ring
end QEC.Distillation.OneQubitMagic
