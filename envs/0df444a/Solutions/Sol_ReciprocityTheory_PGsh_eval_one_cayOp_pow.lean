-- Prove2me | solution 1 for ReciprocityTheory.PGsh.eval_one_cayOp_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:34:21.819346+00:00
-- url     : https://prove2.me/submissions/a24f5261-57ae-49a2-9203-f91fa37d2e4e

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_prod_det_funMat
import Theorems.Thm_ReciprocityTheory_PGsh_eval_fibOp_cayDet
import Theorems.Thm_ReciprocityTheory_PGsh_cayMono_pow
import Theorems.Thm_ReciprocityTheory_PGsh_sum_prod_factorial_fibres

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
namespace ReciprocityTheory.PGsh
theorem _root_.solution (s : ℕ) :
    eval onePt (cayOp n ℤ (cayDet n ℤ ^ s)) = ((∏ k ∈ range n, (s + k) : ℕ) : ℤ) := by
  have hstab : ∀ φ : Fin n → Fin s, ∑ σ : Equiv.Perm (Fin n),
      (if φ ∘ σ = φ then (1 : ℤ) else 0) = ∏ k, ((#{a | φ a = k}).factorial : ℤ) := by
    intro φ
    rw [Finset.sum_boole]
    have h := DomMulAct.stabilizer_card φ
    simp only [Fintype.card_subtype] at h
    exact_mod_cast h
  have h1 : ∀ σ : Equiv.Perm (Fin n), eval onePt (cayMono n ℤ σ (cayDet n ℤ ^ s)) =
      ∑ φ : Fin n → Fin s, if φ ∘ σ = φ then (Equiv.Perm.sign σ : ℤ) else 0 := by
    intro σ
    rw [cayMono_pow, map_sum]
    simp only [map_prod, eval_fibOp_cayDet, prod_det_funMat]
  have hsq : ∀ σ : Equiv.Perm (Fin n),
      (Equiv.Perm.sign σ : ℤ) * (Equiv.Perm.sign σ : ℤ) = 1 := fun σ => by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  simp only [cayOp, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, h1,
    Finset.smul_sum, smul_ite, smul_zero, smul_eq_mul, Finset.mul_sum, mul_ite, mul_zero, hsq]
  rw [Finset.sum_comm]
  simp only [hstab]
  have h2 := sum_prod_factorial_fibres s n
  exact_mod_cast h2
end ReciprocityTheory.PGsh
