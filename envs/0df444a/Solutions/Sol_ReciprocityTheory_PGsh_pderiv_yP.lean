-- Prove2me | solution 1 for ReciprocityTheory.PGsh.pderiv_yP
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:40:49.010884+00:00
-- url     : https://prove2.me/submissions/cceffa13-bc8d-4e9a-ba95-f485f57f5b5a

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow
import Theorems.Thm_ReciprocityTheory_PGsh_deriv_finsetProd

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
theorem _root_.solution (σ τ : Fin n → Fin n) (S : Finset (Fin n)) (j : Fin n) (hj : j ∉ S) :
    pderiv (σ j, j) (yP σ τ S) = yP σ τ (insert j S) := by
  rw [yP, yP, deriv_finsetProd, Finset.sum_eq_single j]
  · refine Finset.prod_congr rfl fun b _ => ?_
    by_cases hb : b = j
    · subst hb; simp [hj, pderiv_X, Pi.single_apply]
    · simp [hb, Finset.mem_insert]
  · intro b₀ _ hb₀
    apply Finset.prod_eq_zero (Finset.mem_univ b₀)
    by_cases hS : b₀ ∈ S
    · simp [hS, apply_ite (⇑(pderiv (σ j, j) : Derivation ℤ (MvPolynomial (Fin n × Fin n) ℤ)
        (MvPolynomial (Fin n × Fin n) ℤ))), Derivation.map_one_eq_zero]
    · simp [hS, pderiv_X, Pi.single_apply, hb₀]
  · simp
end ReciprocityTheory.PGsh
