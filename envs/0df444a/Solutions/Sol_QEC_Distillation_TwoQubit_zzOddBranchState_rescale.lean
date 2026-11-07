-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddBranchState_rescale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:54.336824+00:00
-- url     : https://prove2.me/submissions/07f68724-3613-4cc0-bff8-dc036b83871d

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (Real.sqrt (zzOddWeight psi) : Complex) •
        zzOddBranchState psi h =
      zzOddProjector psi := by
  have hsqrt_ne :
      (Real.sqrt (zzOddWeight psi) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 h))
  unfold zzOddBranchState
  rw [smul_smul, mul_inv_cancel₀ hsqrt_ne, one_smul]
end QEC.Distillation.TwoQubit
