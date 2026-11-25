-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_average_ed28bb99e416
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:05:59.338695+00:00
-- url     : https://prove2.me/submissions/c0c3dd4f-c2e8-4986-892f-70883255fde4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootGridLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_sum_fin_pow_26f64c5d5481

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace RootGridLower
theorem _root_.solution {e M : ℕ} (hM : 0 < M) {ω : ℂ} (hω : IsPrimitiveRoot ω M)
    (Q : MvPolynomial (Fin e) ℤ) (hdeg : ∀ i, Q.degreeOf i < M) (j : Fin e →₀ ℕ)
    (hj : ∀ i, j i < M) :
    ∑ k : Fin e → Fin M, eval (fun i => ω ^ (k i : ℕ)) (map (Int.castRingHom ℂ) Q) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) = (M : ℂ) ^ e * ((Q.coeff j : ℤ) : ℂ) := by
  classical
  simp_rw [eval_map, eval₂_eq', Finset.sum_mul]
  rw [Finset.sum_comm]
  have key : ∀ d ∈ Q.support, ∑ k : Fin e → Fin M,
      (Int.castRingHom ℂ) (Q.coeff d) * (∏ i, (ω ^ (k i : ℕ)) ^ d i) *
        ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ) =
      ((Q.coeff d : ℤ) : ℂ) * if d = j then (M : ℂ) ^ e else 0 := by
    intro d hd
    have hdM : ∀ i, d i < M := fun i => lt_of_le_of_lt (monomial_le_degreeOf i hd) (hdeg i)
    have hprod : ∀ k : Fin e → Fin M, (∏ i, (ω ^ (k i : ℕ)) ^ d i) * ∏ i, ((ω ^ j i)⁻¹) ^ (k i : ℕ)
        = ∏ i, (ω ^ d i * (ω ^ j i)⁻¹) ^ (k i : ℕ) := by
      intro k
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm (k i : ℕ)]
    simp_rw [mul_assoc, hprod, ← Finset.mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun i (t : Fin M) => (ω ^ d i * (ω ^ j i)⁻¹) ^ (t : ℕ))]
    simp_rw [RootGridLower.sum_fin_pow hM hω (hdM _) (hj _)]
    split_ifs with hdj
    · subst hdj; simp
    · obtain ⟨i, hi⟩ : ∃ i, d i ≠ j i := by
        by_contra h
        push Not at h
        exact hdj (Finsupp.ext h)
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [Finset.sum_congr rfl key]
  simp_rw [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq']
  split_ifs with hjs
  · simp [mul_comm]
  · rw [MvPolynomial.notMem_support_iff.mp hjs]; simp
end RootGridLower
end GroundTheory.Heights₂.Heights.HilbertSamuel
