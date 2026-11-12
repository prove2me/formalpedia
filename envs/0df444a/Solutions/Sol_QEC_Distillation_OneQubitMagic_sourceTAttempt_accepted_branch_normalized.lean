-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAttempt_accepted_branch_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:22:22.879774+00:00
-- url     : https://prove2.me/submissions/92cf78c3-6dc5-46be-8f18-9b669a7d7dbe

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
    LinearMap.trace Complex TwoQubitSpace sourceTAttempt.acceptedBranch.toOperator = 1 :=
  sourceTAttempt.acceptedBranch.trace_one
end QEC.Distillation.OneQubitMagic
