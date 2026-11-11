-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAttempt_accepted_weight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T16:13:56.39603+00:00
-- url     : https://prove2.me/submissions/4686f24a-a258-4694-bfd8-77b26bdb0242

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
theorem _root_.solution : sourceTAttempt.acceptedWeight = 2 / 3 :=
  sourceTEvenWeight_eq_two_thirds
end QEC.Distillation.OneQubitMagic
