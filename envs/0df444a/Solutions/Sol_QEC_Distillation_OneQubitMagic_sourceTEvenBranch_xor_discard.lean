-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTEvenBranch_xor_discard
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T14:59:26.230607+00:00
-- url     : https://prove2.me/submissions/8b37c07d-3238-49b1-84ab-90bcaf70b98b

import Definitions.Def_QEC_Distillation_Universality_OneQubitMagic
import Definitions.Def_QEC_Distillation_Core_MagicStateProtocol
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Core
import Definitions.Def_QEC_Distillation_Universality_TResourcePhase
import Theorems.Thm_QEC_Distillation_TwoQubit_secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity


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
    (QuantumChannel.comp secondQubitDiscard
      (QuantumChannel.unitaryConj xorTransport)).mapDensity sourceTEvenBranch =
      zzEvenBranchFirstDensity sourceTTwoQubitState sourceTEvenWeight_pos := by
  exact secondQubitDiscard_mapDensity_xor_zzEvenBranchDensity
    sourceTTwoQubitState sourceTEvenWeight_pos
end QEC.Distillation.OneQubitMagic
