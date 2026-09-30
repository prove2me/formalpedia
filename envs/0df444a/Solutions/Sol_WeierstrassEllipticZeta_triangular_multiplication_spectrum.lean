-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_multiplication_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-10T00:00:08.206527+00:00
-- url     : https://prove2.me/submissions/b5c20f25-b3cc-4c10-9b32-2418fb7d0c4a

import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

noncomputable section


theorem solution
    (V : Finset (Fin 4 → ℂ)) (e : V → ℕ) (d : ℕ)
    (ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin d) (Fin d) ℂ)
    (hdet : ∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).det = ∏ v : V, (MvPolynomial.eval v.val p) ^ e v) :
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).charpoly = ∏ v : V,
        (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^ e v) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (ρ p).trace = ∑ v : V, (e v : ℂ) * MvPolynomial.eval v.val p) ∧
    (∀ (p : MvPolynomial (Fin 4) ℂ) (z : ℂ),
      z ∈ spectrum ℂ (ρ p) ↔ ∃ v : V, 0 < e v ∧ z = MvPolynomial.eval v.val p) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      IsNilpotent (ρ p) ↔ ∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0) ∧
    (∀ p : MvPolynomial (Fin 4) ℂ,
      (∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0) → (ρ p) ^ d = 0) := by
  classical
  have hchar (p : MvPolynomial (Fin 4) ℂ) :
      (ρ p).charpoly = ∏ v : V,
        (Polynomial.X - Polynomial.C (MvPolynomial.eval v.val p)) ^ e v := by
    apply Polynomial.funext
    intro z
    rw [Matrix.eval_charpoly]
    have hscalar : Matrix.scalar (Fin d) z = ρ (MvPolynomial.C z) := by
      simp [Matrix.scalar, Matrix.algebraMap_eq_diagonal]
    rw [hscalar, ← map_sub, hdet]
    simp [Polynomial.eval_prod]
  have hdim : d = ∑ v : V, e v := by
    have h := congrArg Polynomial.natDegree (hchar 0)
    rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      Polynomial.natDegree_prod_of_monic] at h
    · simpa using h
    · intro v _
      exact (Polynomial.monic_X_sub_C _).pow _
  have hspectrum (p : MvPolynomial (Fin 4) ℂ) (z : ℂ) :
      z ∈ spectrum ℂ (ρ p) ↔ ∃ v : V, 0 < e v ∧ z = MvPolynomial.eval v.val p := by
    rw [Matrix.mem_spectrum_iff_isRoot_charpoly, hchar]
    simp [Polynomial.IsRoot, Polynomial.eval_prod, Finset.prod_eq_zero_iff,
      sub_eq_zero, Nat.pos_iff_ne_zero, and_comm]
  have hpower (p : MvPolynomial (Fin 4) ℂ)
      (hp : ∀ v : V, 0 < e v → MvPolynomial.eval v.val p = 0) : (ρ p) ^ d = 0 := by
    have hc : (ρ p).charpoly = Polynomial.X ^ d := by
      rw [hchar, hdim, ← Finset.prod_pow_eq_pow_sum]
      apply Finset.prod_congr rfl
      intro v _
      by_cases hv : e v = 0
      · simp [hv]
      · simp [hp v (Nat.pos_of_ne_zero hv)]
    have h := Matrix.aeval_self_charpoly (ρ p)
    rw [hc] at h
    simpa using h
  refine ⟨hchar, ?_, hspectrum, ?_, hpower⟩
  · intro p
    have hsplit : (ρ p).charpoly.Splits := by
      rw [hchar]
      exact Polynomial.Splits.prod (fun v _ => (Polynomial.Splits.X_sub_C _).pow _)
    rw [Matrix.trace_eq_sum_roots_charpoly_of_splits hsplit, hchar,
      Polynomial.roots_prod _ _ (by
        exact (Polynomial.monic_prod_of_monic _ _
          (fun v _ => (Polynomial.monic_X_sub_C _).pow _)).ne_zero)]
    simp only [Polynomial.roots_pow, Polynomial.roots_X_sub_C,
      Multiset.sum_bind, Multiset.sum_nsmul, Multiset.sum_singleton, nsmul_eq_mul]
    rfl
  · intro p
    refine ⟨?_, fun hp => ⟨d, hpower p hp⟩⟩
    intro hp v hv
    have hc : (ρ p).charpoly = Polynomial.X ^ d := by
      simpa using sub_eq_zero.mp
        (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hp).eq_zero
    have hroot := Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      ((hspectrum p (MvPolynomial.eval v.val p)).mpr ⟨v, hv, rfl⟩)
    rw [hc] at hroot
    exact eq_zero_of_pow_eq_zero (by simpa [Polynomial.IsRoot] using hroot)

