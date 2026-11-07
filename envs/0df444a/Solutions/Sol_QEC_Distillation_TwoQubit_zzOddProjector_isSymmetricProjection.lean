-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddProjector_isSymmetricProjection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:01:46.762863+00:00
-- url     : https://prove2.me/submissions/a98b0e12-1837-42bb-a716-85e23ff5d1d4

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Clifford
import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_adjoint
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_idempotent

set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open Semantics Semantics.Qubit
namespace QEC.Distillation.TwoQubit
theorem _root_.solution :
    zzOddProjector.IsSymmetricProjection := by
  refine ⟨zzOddProjector_idempotent, ?_⟩
  rw [LinearMap.isSymmetric_iff_isSelfAdjoint]
  exact zzOddProjector_adjoint
end QEC.Distillation.TwoQubit
