-- Prove2me | solution 1 for QEC.Distillation.OneQubitMagic.sourceTSin_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T05:22:10.660483+00:00
-- url     : https://prove2.me/submissions/be2347b2-2e5c-4d6c-9274-f47048af2666

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
theorem _root_.solution : 0 ≤ sourceTSin := by
  unfold sourceTSin
  apply div_nonneg sourceTParameter_nonneg
  exact mul_nonneg (le_of_lt sqrt_two_pos) (le_of_lt sourceTCos_pos)
end QEC.Distillation.OneQubitMagic
