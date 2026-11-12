-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAttempt_rejected_branch_normalized
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:22:26.796199+00:00
-- url     : https://prove2.me/submissions/07be4b13-7fae-4cd7-99e0-1bc774267640

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
    LinearMap.trace Complex TwoQubitSpace sourceTAttempt.rejectedBranch.toOperator = 1 :=
  sourceTAttempt.rejectedBranch.trace_one
end QEC.Distillation.OneQubitMagic
