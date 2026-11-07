-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddBranchDensity_toOperator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:19.940497+00:00
-- url     : https://prove2.me/submissions/3cee3fc4-0166-407c-80fb-e43b8add6a1f

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
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    (zzOddBranchDensity psi h).toOperator =
      (InnerProductSpace.rankOne Complex
        (zzOddBranchState psi h)
        (zzOddBranchState psi h)).toLinearMap := by
  rw [zzOddBranchDensity, DensityOperator.pureOfNonzero_toOperator]
  rw [inner_self_eq_norm_sq_to_K, zzOddBranchState_norm]
  norm_num
end QEC.Distillation.TwoQubit
