-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_multiplication_matrix
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T23:11:06.055016+00:00
-- url     : https://prove2.me/submissions/f48aaf01-114e-4960-9790-f3eacba0fb18

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

noncomputable section


theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (M : Polynomial ℂ)
    (hM : M.Monic) (r : Fin 3 → Polynomial ℂ)
    (hmem : ∀ p : MvPolynomial (Fin 4) ℂ,
      p ∈ I ↔ M ∣ MvPolynomial.aeval (Fin.cons Polynomial.X r) p)
    (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (hunique : ∀ (p : MvPolynomial (Fin 4) ℂ) (b : Polynomial ℂ),
      b.degree < (M.natDegree : ℕ) →
      p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I → b = T p)
    (β : Module.Basis (Fin M.natDegree) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I))
    (hβ : ∀ j : Fin M.natDegree,
      β j = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ j.val * q))
    (hcoord : ∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin M.natDegree),
      β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) :
    ∃ ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ,
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Algebra.leftMulMatrix β (Ideal.Quotient.mk I p)) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i j : Fin M.natDegree),
        ρ p i j = ((MvPolynomial.aeval (Fin.cons Polynomial.X r) p *
          Polynomial.X ^ j.val) %ₘ M).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ, ρ p = 0 ↔ p ∈ I) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        ρ p = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4)))
          (MvPolynomial.aeval (Fin.cons Polynomial.X r) p)) ∧
      (ρ (MvPolynomial.X (0 : Fin 4))).charpoly = M := by
  classical
  let φ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Polynomial ℂ :=
    MvPolynomial.aeval (Fin.cons Polynomial.X r)
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  have hE : φ.comp E = AlgHom.id ℂ (Polynomial ℂ) := by
    ext
    simp [φ, E]
  have hEapp (f : Polynomial ℂ) : φ (E f) = f := AlgHom.congr_fun hE f
  have hx : φ (MvPolynomial.X (0 : Fin 4)) = Polynomial.X := by simp [φ]
  let ρ : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] Matrix (Fin M.natDegree) (Fin M.natDegree) ℂ :=
    (Algebra.leftMulMatrix β).comp (Ideal.Quotient.mkₐ ℂ I)
  have hzero (p : MvPolynomial (Fin 4) ℂ) : ρ p = 0 ↔ p ∈ I := by
    change Algebra.leftMulMatrix β (Ideal.Quotient.mk I p) = 0 ↔ p ∈ I
    rw [← (Algebra.leftMulMatrix β).map_zero]
    change Algebra.leftMulMatrix β (Ideal.Quotient.mk I p) = Algebra.leftMulMatrix β 0 ↔ p ∈ I
    rw [(Algebra.leftMulMatrix_injective β).eq_iff]
    exact Ideal.Quotient.eq_zero_iff_mem
  have hρE (f : Polynomial ℂ) :
      ρ (E f) = Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4))) f :=
    (Polynomial.aeval_algHom_apply ρ (MvPolynomial.X (0 : Fin 4)) f).symm
  have hann (f : Polynomial ℂ) :
      Polynomial.aeval (ρ (MvPolynomial.X (0 : Fin 4))) f = 0 ↔ M ∣ f := by
    rw [← hρE, hzero, hmem]
    change M ∣ φ (E f) ↔ M ∣ f
    rw [hEapp]
  have hred (f : MvPolynomial (Fin 4) ℂ) : f - E (φ f %ₘ M) ∈ I := by
    apply (hmem _).mpr
    change M ∣ φ (f - E (φ f %ₘ M))
    rw [map_sub, hEapp, Polynomial.modByMonic_eq_sub_mul_div, sub_sub_cancel]
    exact dvd_mul_right _ _
  have hdiv (p : MvPolynomial (Fin 4) ℂ) (j : Fin M.natDegree) :
      T (p * ((MvPolynomial.X (0 : Fin 4)) ^ j.val * q)) =
        (φ p * Polynomial.X ^ j.val) %ₘ M := by
    apply (hunique _ _ ?_ ?_).symm
    · simpa only [Polynomial.degree_eq_natDegree hM.ne_zero] using
        Polynomial.degree_modByMonic_lt (φ p * Polynomial.X ^ j.val) hM
    · have hz := Ideal.mul_mem_right q I (hred (p * (MvPolynomial.X (0 : Fin 4)) ^ j.val))
      rw [map_mul, map_pow, hx] at hz
      convert hz using 1
      ring
  refine ⟨ρ, fun _ => rfl, ?_, hzero, ?_, ?_⟩
  · intro p i j
    change Algebra.leftMulMatrix β (Ideal.Quotient.mk I p) i j = _
    rw [Algebra.leftMulMatrix_eq_repr_mul, hβ, ← map_mul, hcoord, hdiv]
  · intro p
    have hp : p - E (φ p) ∈ I := by
      apply (hmem _).mpr
      change M ∣ φ (p - E (φ p))
      rw [map_sub, hEapp, sub_self]
      exact dvd_zero M
    have hz := (hzero _).mpr hp
    rw [map_sub, hρE] at hz
    exact sub_eq_zero.mp hz
  · apply Polynomial.eq_of_monic_of_dvd_of_natDegree_le hM (Matrix.charpoly_monic _)
    · exact (hann _).mp (Matrix.aeval_self_charpoly _)
    · simp only [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, le_refl]

