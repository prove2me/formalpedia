-- Prove2me | solution 1 for WeierstrassEllipticZeta.bounded_time_bezout_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T00:30:34.417423+00:00
-- url     : https://prove2.me/submissions/ee35c4aa-be64-4f6c-9fcd-80d917d2dfc2

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.Tactic.Ring

noncomputable section


private lemma time_polynomial_totalDegree (p : Polynomial ℂ) :
    (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) p).totalDegree ≤ p.natDegree := by
  classical
  rw [Polynomial.aeval_eq_sum_range]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i hi
  refine (MvPolynomial.totalDegree_smul_le _ _).trans ?_
  rw [MvPolynomial.totalDegree_X_pow]
  exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)

theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (M : Polynomial ℂ)
    (hM : M.Monic) (hdegree : M.degree = (d : ℕ)) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (K : ℕ) (f a : Fin K → MvPolynomial (Fin 4) ℂ)
    (ha : 1 - ∑ j : Fin K, a j * f j ∈ I) :
    ∃ b : Fin K → Polynomial ℂ,
      (∀ j : Fin K, (b j).degree < (d : ℕ) ∧
        (Polynomial.aeval (MvPolynomial.X (R := ℂ) (0 : Fin 4)) (b j)).totalDegree ≤ d - 1 ∧
        a j - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) ∈ I) ∧
      1 - ∑ j : Fin K,
        Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * f j ∈ I ∧
      ∀ D : ℕ, (∀ j : Fin K, (f j).totalDegree ≤ D) →
        (1 - ∑ j : Fin K,
          Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (b j) * f j).totalDegree ≤ d - 1 + D := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  let b : Fin K → Polynomial ℂ := fun j => φ (a j) %ₘ M
  have hcongr (j : Fin K) : a j - E (b j) ∈ I := by
    apply (hmem _).mpr
    change M ∣ φ (a j - E (b j))
    have he : φ (E (b j)) = b j := AlgHom.congr_fun hE (b j)
    rw [map_sub, he]
    dsimp [b]
    rw [Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
    exact dvd_mul_right _ _
  have hsmall (j : Fin K) : (b j).degree < (d : ℕ) ∧ (E (b j)).totalDegree ≤ d - 1 := by
    have hdeg : (b j).degree < (d : ℕ) := by
      simpa only [b, hdegree] using Polynomial.degree_modByMonic_lt (φ (a j)) hM
    refine ⟨hdeg, ?_⟩
    apply (time_polynomial_totalDegree (b j)).trans
    by_cases hb : b j = 0
    · simp [hb]
    · exact Nat.le_sub_one_of_lt ((Polynomial.natDegree_lt_iff_degree_lt hb).mpr hdeg)
  refine ⟨b, fun j => ⟨(hsmall j).1, (hsmall j).2, hcongr j⟩, ?_, ?_⟩
  · have hsum : ∑ j : Fin K, (a j - E (b j)) * f j ∈ I :=
      Submodule.sum_mem _ fun j _ => Ideal.mul_mem_right _ _ (hcongr j)
    have heq : 1 - ∑ j : Fin K, E (b j) * f j =
        (1 - ∑ j : Fin K, a j * f j) + ∑ j : Fin K, (a j - E (b j)) * f j := by
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring
    change 1 - ∑ j : Fin K, E (b j) * f j ∈ I
    rw [heq]
    exact I.add_mem ha hsum
  · intro D hD
    have hsum : (∑ j : Fin K, E (b j) * f j).totalDegree ≤ d - 1 + D := by
      apply MvPolynomial.totalDegree_finsetSum_le
      intro j _
      exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hsmall j).2 (hD j))
    change (1 - ∑ j : Fin K, E (b j) * f j).totalDegree ≤ d - 1 + D
    rw [sub_eq_add_neg]
    apply (MvPolynomial.totalDegree_add _ _).trans
    refine max_le (by simp) ?_
    simpa only [neg_one_smul] using
      (MvPolynomial.totalDegree_smul_le (-1 : ℂ) (∑ j : Fin K, E (b j) * f j)).trans hsum

