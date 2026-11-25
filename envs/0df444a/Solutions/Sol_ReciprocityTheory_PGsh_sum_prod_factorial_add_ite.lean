-- Prove2me | solution 1 for ReciprocityTheory.PGsh.sum_prod_factorial_add_ite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T15:44:17.539815+00:00
-- url     : https://prove2.me/submissions/8f09929d-18bc-4770-b2ef-cb409528afd8

import Definitions.Def_ReciprocityTheory_DualLattices_FischerAdjointStatement
import Definitions.Def_ReciprocityTheory_DualLattices_DetPolyMulCayleyOmegaPow

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
theorem _root_.solution {s : ℕ} (c : Fin s → ℕ) :
    ∑ k₀, ∏ k, (c k + if k₀ = k then 1 else 0).factorial =
      (∏ k, (c k).factorial) * (∑ k, c k + s) := by
  have h : ∀ k₀, ∏ k, (c k + if k₀ = k then 1 else 0).factorial =
      (∏ k, (c k).factorial) * (c k₀ + 1) := by
    intro k₀
    have e : ∀ k, (c k + if k₀ = k then 1 else 0).factorial =
        (c k).factorial * (if k₀ = k then c k + 1 else 1) := by
      intro k
      split_ifs
      · rw [Nat.factorial_succ, mul_comm]
      · simp
    simp only [e, Finset.prod_mul_distrib, Finset.prod_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_congr rfl fun k₀ _ => h k₀, ← Finset.mul_sum, Finset.sum_add_distrib]
  simp
end ReciprocityTheory.PGsh
