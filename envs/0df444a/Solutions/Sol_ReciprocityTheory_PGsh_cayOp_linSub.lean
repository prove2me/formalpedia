-- Prove2me | solution 1 for ReciprocityTheory.PGsh.cayOp_linSub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:27:25.270264+00:00
-- url     : https://prove2.me/submissions/9475361a-fb3e-410e-9b59-965a84291c16

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_dOp_linSub
import Theorems.Thm_ReciprocityTheory_PGsh_cayMono_eq_dOp
import Theorems.Thm_ReciprocityTheory_PGsh_sum_fun_eq_sum_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Matrix Finset
open ReciprocityTheory ReciprocityTheory.PGsh
variable {n : ℕ}
variable {R : Type*} [CommRing R]
namespace ReciprocityTheory.PGsh
theorem _root_.solution (g : Matrix (Fin n) (Fin n) R) (q : MvPolynomial (Fin n × Fin n) R) :
    cayOp n R (linSub g q) = C g.det * linSub g (cayOp n R q) := by
  have hdet : ∀ τ : Fin n → Fin n, ∑ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) • ∏ t, g (τ t) (σ t) = (g.submatrix τ id).det := by
    intro τ
    rw [← Matrix.det_transpose, Matrix.det_apply]
    simp [Units.smul_def]
  have h0 : ∀ τ : Fin n → Fin n, ¬ Function.Injective τ → (g.submatrix τ id).det = 0 := by
    intro τ hτ
    simp only [Function.Injective, not_forall] at hτ
    obtain ⟨i, j, hij, hne⟩ := hτ
    exact Matrix.det_zero_of_row_eq hne (by ext k; simp [hij])
  calc cayOp n R (linSub g q)
      = ∑ σ : Equiv.Perm (Fin n), ∑ τ : Fin n → Fin n,
          C ((Equiv.Perm.sign σ : ℤ) • ∏ t, g (τ t) (σ t)) * linSub g (dOp τ id q) := by
        simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, cayMono_eq_dOp, dOp_linSub,
          Finset.smul_sum, map_zsmul, smul_mul_assoc]
    _ = ∑ τ : Fin n → Fin n, C ((g.submatrix τ id).det) * linSub g (dOp τ id q) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← hdet, map_sum, Finset.sum_mul]
    _ = ∑ e : Equiv.Perm (Fin n), C ((g.submatrix e id).det) * linSub g (dOp e id q) :=
        sum_fun_eq_sum_perm _ fun τ hτ => by rw [h0 τ hτ, map_zero, zero_mul]
    _ = C g.det * linSub g (cayOp n R q) := by
        simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, cayMono_eq_dOp, map_sum,
          Finset.mul_sum, Matrix.det_permute, map_zsmul, map_mul, map_intCast]
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [zsmul_eq_mul]
        ring
end ReciprocityTheory.PGsh
