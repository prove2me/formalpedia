-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T15:03:15.65521+00:00
-- url     : https://prove2.me/submissions/831e511b-649b-4428-82d8-af6f61c87374

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
theorem _root_.solution : sourceTAttempt.rejectedWeight = 1 / 3 :=
  sourceTOddWeight_eq_one_third
end QEC.Distillation.OneQubitMagic
