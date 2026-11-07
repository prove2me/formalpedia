-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddProjector_branchState
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:17.03298+00:00
-- url     : https://prove2.me/submissions/7ea28ea1-1df9-43a9-884c-59d36655a45c

import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Definitions.Def_QEC_Semantics_ErrorCorrection_CodeSupport
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityBranches
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_idempotent


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics
namespace QEC.Distillation.TwoQubit
theorem _root_.solution
    (psi : TwoQubitSpace) (h : 0 < zzOddWeight psi) :
    zzOddProjector (zzOddBranchState psi h) =
      zzOddBranchState psi h := by
  unfold zzOddBranchState
  rw [LinearMap.map_smul]
  congr 1
  rw [← Module.End.mul_apply, zzOddProjector_idempotent]
end QEC.Distillation.TwoQubit
