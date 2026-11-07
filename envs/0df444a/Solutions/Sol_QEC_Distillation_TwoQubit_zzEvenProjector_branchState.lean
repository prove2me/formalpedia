-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenProjector_branchState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:15.675541+00:00
-- url     : https://prove2.me/submissions/9cb88cdf-85d0-4c36-914c-4086f39a95fe

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_idempotent


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (h : 0 < zzEvenWeight psi) :
    zzEvenProjector (zzEvenBranchState psi h) =
      zzEvenBranchState psi h := by
  unfold zzEvenBranchState
  rw [LinearMap.map_smul]
  congr 1
  rw [← Module.End.mul_apply, zzEvenProjector_idempotent]
end QEC.Distillation.TwoQubit
