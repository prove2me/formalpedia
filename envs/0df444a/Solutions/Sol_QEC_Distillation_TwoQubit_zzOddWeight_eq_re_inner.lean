-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzOddWeight_eq_re_inner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:04:01.219099+00:00
-- url     : https://prove2.me/submissions/bcc0adf3-f6b9-47b0-a9fd-64dbd8bf8600

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_idempotent
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddProjector_isSymmetricProjection


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    zzOddWeight psi =
      Complex.re ⟪psi, zzOddProjector psi⟫_ℂ := by
  unfold zzOddWeight
  calc
    ‖zzOddProjector psi‖ ^ 2 =
        Complex.re
          ⟪zzOddProjector psi, zzOddProjector psi⟫_ℂ :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) _
    _ = Complex.re
          ⟪psi, zzOddProjector (zzOddProjector psi)⟫_ℂ :=
      congrArg Complex.re
        (zzOddProjector_isSymmetricProjection.isSymmetric
          psi (zzOddProjector psi))
    _ = Complex.re ⟪psi, zzOddProjector psi⟫_ℂ := by
      rw [← Module.End.mul_apply, zzOddProjector_idempotent]
end QEC.Distillation.TwoQubit
