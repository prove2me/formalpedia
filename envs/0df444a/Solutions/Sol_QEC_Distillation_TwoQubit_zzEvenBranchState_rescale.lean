-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenBranchState_rescale
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:18:46.937685+00:00
-- url     : https://prove2.me/submissions/c9504db6-f070-4d04-8dc4-f9d998a361d7

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
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (Real.sqrt (zzEvenWeight psi) : Complex) •
        zzEvenBranchState psi h =
      zzEvenProjector psi := by
  have hsqrt_ne :
      (Real.sqrt (zzEvenWeight psi) : Complex) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 h))
  unfold zzEvenBranchState
  rw [smul_smul, mul_inv_cancel₀ hsqrt_ne, one_smul]
end QEC.Distillation.TwoQubit
