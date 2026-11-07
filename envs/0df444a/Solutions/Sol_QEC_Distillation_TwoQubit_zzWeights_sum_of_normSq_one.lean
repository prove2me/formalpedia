-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzWeights_sum_of_normSq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:42.228938+00:00
-- url     : https://prove2.me/submissions/ae07c474-5096-46fe-bc1d-d4ed9c44cc9a

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Theorems.Thm_QEC_Distillation_TwoQubit_zzWeights_sum

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (hpsi : ‖psi‖ ^ 2 = 1) :
    zzEvenWeight psi + zzOddWeight psi = 1 := by
  calc
    zzEvenWeight psi + zzOddWeight psi = ‖psi‖ ^ 2 :=
      zzWeights_sum psi
    _ = 1 := hpsi
end QEC.Distillation.TwoQubit
