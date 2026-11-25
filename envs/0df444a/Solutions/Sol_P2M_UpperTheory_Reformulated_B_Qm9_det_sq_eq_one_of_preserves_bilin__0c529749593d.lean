-- Prove2me | solution 1 for P2M_UpperTheory_Reformulated_B_Qm9_det_sq_eq_one_of_preserves_bilin__0c529749593d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:00:33.850483+00:00
-- url     : https://prove2.me/submissions/f5890d79-547d-44cd-80d6-048724c13214

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_DetSqEqOneOfPreservesBilin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin
theorem _root_.solution.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℝ V] [FiniteDimensional ℝ V] (B : LinearMap.BilinForm ℝ V),
    B.Nondegenerate →
      ∀ (f : V →ₗ[ℝ] V),
        (∀ (x y : V), ((B : V → V →ₗ[ℝ] ℝ) ((f : V → V) x) : V → ℝ) ((f : V → V) y) = ((B : V → V →ₗ[ℝ] ℝ) x : V → ℝ) y) →
          (LinearMap.det : (V →ₗ[ℝ] V) → ℝ) f ^ (2 : ℕ) = (1 : ℝ) := by
  intro V _ _ _ B hB f hf
  classical
  let b := Module.finBasis ℝ V
  have hcomp : B.comp f f = B := by
    ext x y
    simpa using hf x y
  have hmat := LinearMap.BilinForm.toMatrix_comp b b B f f
  rw [hcomp] at hmat
  have hne : (LinearMap.BilinForm.toMatrix b B).det ≠ 0 :=
    (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero b).mp hB
  have hdet := congrArg Matrix.det hmat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, LinearMap.det_toMatrix] at hdet
  apply mul_left_cancel₀ hne
  linear_combination -hdet
end UpperTheory.Reformulated.B.Qm9.det_sq_eq_one_of_preserves_bilin
