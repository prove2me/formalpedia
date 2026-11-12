-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTAccepted_emits_output
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T15:00:11.869207+00:00
-- url     : https://prove2.me/submissions/c9b1db71-6549-4af6-8203-e3d59410c963

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
    sourceTOutcomeAction .accepted = .emitAccepted := rfl
end QEC.Distillation.OneQubitMagic
