-- Prove2me | solution 1 for WalledBrauer.Center.lemma_3_4
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-22T03:33:38.065078+00:00
-- url     : https://prove2.me/submissions/30047a52-4497-4527-ae3f-cecebc600854

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Choose

set_option autoImplicit false
open MvPolynomial
open scoped BigOperators

theorem solution (m n : ℕ) (hn : 0 < n) (S : Subalgebra ℂ (MvPolynomial (Fin m) ℂ))
    (k : Fin n → Fin m → ℂ)
    (hsep : ∀ i j : Fin n, i ≠ j → ∃ p ∈ S, eval (k i) p ≠ eval (k j) p) :
    ∃ P : Fin n → MvPolynomial (Fin m) ℂ,
      (∀ i, P i ∈ S) ∧ (Matrix.of fun i j => eval (k j) (P i)).det ≠ 0 := by
  classical
  have hb : ∀ i : Fin n, ∃ P ∈ S,
      ∀ j : Fin n, eval (k j) P = if i = j then 1 else 0 := by
    intro i
    have hfactor : ∀ j : {j : Fin n // j ≠ i}, ∃ q ∈ S,
        eval (k i) q = 1 ∧ eval (k j) q = 0 := by
      intro j
      obtain ⟨p, hp, hne⟩ := hsep i j j.property.symm
      let a := eval (k i) p - eval (k j) p
      have ha : a ≠ 0 := sub_ne_zero.mpr hne
      have hC : ∀ z : ℂ, C z ∈ S := by
        intro z
        simpa only [MvPolynomial.algebraMap_eq] using S.algebraMap_mem z
      refine ⟨C a⁻¹ * (p - C (eval (k j) p)),
        S.mul_mem (hC _) (S.sub_mem hp (hC _)), ?_, ?_⟩
      · simpa only [map_mul, map_sub, eval_C] using inv_mul_cancel₀ ha
      · simp only [map_mul, map_sub, eval_C, sub_self, mul_zero]
    choose q hq hqi hqj using hfactor
    refine ⟨∏ j, q j, S.prod_mem (fun j _ => hq j), ?_⟩
    intro j
    rw [eval_prod]
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact Finset.prod_eq_one (fun t _ => hqi t)
    · rw [if_neg hij]
      exact Finset.prod_eq_zero (Finset.mem_univ ⟨j, Ne.symm hij⟩) (hqj ⟨j, Ne.symm hij⟩)
  choose P hPS hPeval using hb
  refine ⟨P, hPS, ?_⟩
  have hmat : (Matrix.of fun i j => eval (k j) (P i)) = (1 : Matrix (Fin n) (Fin n) ℂ) := by
    ext i j
    simp only [Matrix.of_apply, Matrix.one_apply, hPeval]
  rw [hmat, Matrix.det_one]
  exact one_ne_zero

#print axioms solution
