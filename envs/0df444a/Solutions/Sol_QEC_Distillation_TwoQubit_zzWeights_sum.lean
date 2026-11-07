-- Prove2me | solution 1 for QEC.Distillation.TwoQubit.zzWeights_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:07:51.643205+00:00
-- url     : https://prove2.me/submissions/26c25161-362a-47e2-bb99-1e04fc2421f4

import Definitions.Def_QEC_Distillation_TwoQubitOperations_Parity
import Definitions.Def_QEC_Distillation_TwoQubitOperations_ParityWeights
import Theorems.Thm_QEC_Distillation_TwoQubit_zzEvenWeight_eq_re_inner
import Theorems.Thm_QEC_Distillation_TwoQubit_zzOddWeight_eq_re_inner
import Theorems.Thm_QEC_Distillation_TwoQubit_zzProjectors_complete


set_option autoImplicit false
noncomputable section
open QEC
open QEC.Distillation
open QEC.Distillation.TwoQubit
open scoped InnerProductSpace
namespace QEC.Distillation.TwoQubit
theorem _root_.solution (psi : TwoQubitSpace) :
    zzEvenWeight psi + zzOddWeight psi = ‖psi‖ ^ 2 := by
  rw [zzEvenWeight_eq_re_inner, zzOddWeight_eq_re_inner]
  calc
    Complex.re ⟪psi, zzEvenProjector psi⟫_ℂ +
          Complex.re ⟪psi, zzOddProjector psi⟫_ℂ =
        Complex.re
          (⟪psi, zzEvenProjector psi⟫_ℂ +
            ⟪psi, zzOddProjector psi⟫_ℂ) := by
      rw [Complex.add_re]
    _ = Complex.re
          ⟪psi, zzEvenProjector psi + zzOddProjector psi⟫_ℂ := by
      rw [inner_add_right]
    _ = Complex.re
          ⟪psi, (zzEvenProjector + zzOddProjector) psi⟫_ℂ := rfl
    _ = Complex.re ⟪psi, psi⟫_ℂ := by
      rw [zzProjectors_complete]
      rfl
    _ = ‖psi‖ ^ 2 :=
      (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := Complex) psi).symm
end QEC.Distillation.TwoQubit
