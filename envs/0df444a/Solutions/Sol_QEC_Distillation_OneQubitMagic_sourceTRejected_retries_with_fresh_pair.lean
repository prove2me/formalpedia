-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTRejected_retries_with_fresh_pair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:00:08.482095+00:00
-- url     : https://prove2.me/submissions/6b50dddb-27a9-47ae-b666-f0d939e3764f

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
    sourceTOutcomeAction .rejected = .retryWithFreshPair := rfl
end QEC.Distillation.OneQubitMagic
