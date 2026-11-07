-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzEvenWeight_eq_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:03:51.04144+00:00
-- url     : https://prove2.me/submissions/d82dbf83-2306-46a2-a25c-505721666bf4

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_idempotent
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenProjector_isSymmetricProjection


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    zzEvenWeight psi =
      Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ := by
  unfold zzEvenWeight
  calc
    ‖zzEvenProjector psi‖ ^ 2 =
        Complex.re
          ⟪zzEvenProjector psi, zzEvenProjector psi⟫_ℂ :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) _
    _ = Complex.re
          ⟪psi, zzEvenProjector (zzEvenProjector psi)⟫_ℂ :=
      congrArg Complex.re
        (zzEvenProjector_isSymmetricProjection.isSymmetric
          psi (zzEvenProjector psi))
    _ = Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ := by
      rw [← Module.End.mul_apply, zzEvenProjector_idempotent]
end QEC.Distillation.TwoQubit
