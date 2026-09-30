-- Prove2me | solution 1 for TranscendenceTheory.bihomogeneous_lift_four_variables
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-08T13:53:52.826225+00:00
-- url     : https://prove2.me/submissions/fe48159d-f30c-4a20-98bc-14b7b6f4e986

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring

noncomputable section
open MvPolynomial


private def p2m_paddedExponent (m n : ℕ) (d : Fin 4 →₀ ℕ) : Fin 7 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm
    ![m - d 0, d 0, n - (d 1 + d 2 + d 3), d 1, d 2, d 3, 0]

private lemma p2m_paddedExponent_degrees (m n : ℕ) (d : Fin 4 →₀ ℕ)
    (hm : d 0 ≤ m) (hn : d 1 + d 2 + d 3 ≤ n) :
    (p2m_paddedExponent m n d) 0 + (p2m_paddedExponent m n d) 1 = m ∧
      (p2m_paddedExponent m n d) 2 + (p2m_paddedExponent m n d) 3 +
        (p2m_paddedExponent m n d) 4 + (p2m_paddedExponent m n d) 5 +
          (p2m_paddedExponent m n d) 6 = n ∧ (p2m_paddedExponent m n d) 6 = 0 := by
  simp [p2m_paddedExponent]
  omega

private lemma p2m_paddedExponent_eval (R : Type*) [CommSemiring R]
    (m n : ℕ) (d : Fin 4 →₀ ℕ) (hm : d 0 ≤ m) (hn : d 1 + d 2 + d 3 ≤ n)
    (c : R) (x : Fin 4 → R) (r s t : R) :
    eval ![r, r * x 0, s, s * x 1, s * x 2, s * x 3, t]
        (monomial (p2m_paddedExponent m n d) c) =
      r ^ m * s ^ n * (c * ∏ i, x i ^ d i) := by
  rw [eval_monomial, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp [Fin.prod_univ_seven, Fin.prod_univ_four, p2m_paddedExponent, mul_pow]
  have hr : r ^ m = r ^ (m - d 0) * r ^ d 0 := by
    rw [← pow_add, Nat.sub_add_cancel hm]
  have hs : s ^ n = s ^ (n - (d 1 + d 2 + d 3)) *
      s ^ d 1 * s ^ d 2 * s ^ d 3 := by
    simp only [← pow_add]
    congr 1
    omega
  rw [hr, hs]
  ring

theorem solution (R : Type*) [CommSemiring R]
    (P : MvPolynomial (Fin 4) R) (m n : ℕ)
    (hP : ∀ d ∈ P.support, d 0 ≤ m ∧ d 1 + d 2 + d 3 ≤ n) :
    ∃ Q : MvPolynomial (Fin 7) R,
      (∀ d ∈ Q.support, d 0 + d 1 = m ∧
        d 2 + d 3 + d 4 + d 5 + d 6 = n ∧ d 6 = 0) ∧
      ∀ (x : Fin 4 → R) (r s t : R),
        MvPolynomial.eval ![r, r * x 0, s, s * x 1, s * x 2, s * x 3, t] Q =
          r ^ m * s ^ n * MvPolynomial.eval x P := by
  classical
  let Q : MvPolynomial (Fin 7) R :=
    ∑ d ∈ P.support, monomial (p2m_paddedExponent m n d) (P.coeff d)
  refine ⟨Q, ?_, ?_⟩
  · intro d hd
    obtain ⟨e, he, hde⟩ := Finset.mem_biUnion.mp (support_sum hd)
    have hde' : d = p2m_paddedExponent m n e :=
      Finset.mem_singleton.mp (support_monomial_subset hde)
    rw [hde']
    exact p2m_paddedExponent_degrees m n e (hP e he).1 (hP e he).2
  · intro x r s t
    dsimp only [Q]
    rw [map_sum, eval_eq', Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    exact p2m_paddedExponent_eval R m n d (hP d hd).1 (hP d hd).2 (P.coeff d) x r s t

