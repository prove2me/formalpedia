-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAttempt_resource_count
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:02:24.078702+00:00
-- url     : https://prove2.me/submissions/f5a56393-ebcb-4d66-95e7-d64928a52c69

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
theorem _root_.solution : sourceTAttempt.resourceCount = 2 := rfl
end QEC.Distillation.OneQubitMagic
