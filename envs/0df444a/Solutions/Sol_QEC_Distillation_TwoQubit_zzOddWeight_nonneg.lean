-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddWeight_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:39.265706+00:00
-- url     : https://prove2.me/submissions/ef0d0ccd-f902-4132-9097-c65155f53785

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
    0 ≤ zzOddWeight psi :=
  sq_nonneg _
end QEC.Distillation.TwoQubit
