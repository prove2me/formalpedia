-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenBranchDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:06:02.19921+00:00
-- url     : https://prove2.me/submissions/666a1dd2-214a-4af1-8d0e-8a6e05c3f3fd

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
import Theorems.Thm_QEC_Semantics_DensityOperator_pureOfNonzero_toOperator
attribute [local simp] QEC.Semantics.DensityOperator.pureOfNonzero_toOperator



set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    (zzEvenBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzEvenBranchState psi h)
        (zzEvenBranchState psi h)).toLinearMap := by
  rw [zzEvenBranchDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, zzEvenBranchState_norm]
  norm_num
end QEC.Distillation.TwoQubit
