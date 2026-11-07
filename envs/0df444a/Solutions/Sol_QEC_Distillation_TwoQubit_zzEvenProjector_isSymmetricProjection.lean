-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenProjector_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:33.014022+00:00
-- url     : https://prove2.me/submissions/23a38d47-0dcd-487b-a5e4-71c9ee31a75b

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_adjoint
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_idempotent

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
namespace QEC.Distillation.TwoQubit
theorem _root_.solution :
    zzEvenProjector.IsSymmetricProjection := by
  refine ⟨zzEvenProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact zzEvenProjector_adjoint
end QEC.Distillation.TwoQubit
