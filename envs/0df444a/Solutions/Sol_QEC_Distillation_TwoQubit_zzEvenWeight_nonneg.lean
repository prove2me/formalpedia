-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:38.032939+00:00
-- url     : https://prove2.me/submissions/23bf52e7-1895-4beb-b206-917b64397f79

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    0 ≤ zzEvenWeight psi :=
  sq_nonneg _
end QEC.Distillation.TwoQubit
