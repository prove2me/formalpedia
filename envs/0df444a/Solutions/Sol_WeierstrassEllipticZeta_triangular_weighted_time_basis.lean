-- Prove2me | solution 1 for WeierstrassEllipticZeta.triangular_weighted_time_basis
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-09T22:41:05.951549+00:00
-- url     : https://prove2.me/submissions/b7c29511-ee95-4a54-8136-18767d849bcd

import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Polynomial.DegreeLT

noncomputable section


theorem solution
    (I : Ideal (MvPolynomial (Fin 4) ℂ)) (d : ℕ) (q : MvPolynomial (Fin 4) ℂ)
    (T : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial ℂ)
    (hrep : ∀ p : MvPolynomial (Fin 4) ℂ, (T p).degree < (d : ℕ) ∧
      p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) (T p) * q ∈ I ∧
      ∀ b : Polynomial ℂ, b.degree < (d : ℕ) →
        p - Polynomial.aeval (MvPolynomial.X (0 : Fin 4)) b * q ∈ I → b = T p) :
    ∃ β : Module.Basis (Fin d) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I),
      (∀ i : Fin d, β i = Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) ∧
        ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q).totalDegree ≤ d - 1 + q.totalDegree) ∧
      (∀ (p : MvPolynomial (Fin 4) ℂ) (i : Fin d),
        β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val) ∧
      (∀ p : MvPolynomial (Fin 4) ℂ,
        Ideal.Quotient.mk I p = ∑ i : Fin d,
          (T p).coeff i.val • Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)) ∧
      Module.finrank ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) = d := by
  classical
  let E : Polynomial ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
    Polynomial.aeval (MvPolynomial.X (0 : Fin 4))
  let F : MvPolynomial (Fin 4) ℂ →ₗ[ℂ] Polynomial.degreeLT ℂ d :=
    T.codRestrict _ (fun p => Polynomial.mem_degreeLT.mpr (hrep p).1)
  have htime (b : Polynomial.degreeLT ℂ d) : T (E b.val * q) = b.val := by
    have hz : E b.val * q - E b.val * q ∈ I := by rw [sub_self]; exact I.zero_mem
    exact ((hrep (E b.val * q)).2.2 b.val (Polynomial.mem_degreeLT.mp b.property) hz).symm
  have hsurj : Function.Surjective F := by
    intro b
    refine ⟨E b.val * q, Subtype.ext (htime b)⟩
  have hker : LinearMap.ker F = I.restrictScalars ℂ := by
    ext p
    change F p = 0 ↔ p ∈ I
    constructor
    · intro hp
      have hz : T p = 0 := congrArg Subtype.val hp
      simpa only [hz, map_zero, zero_mul, sub_zero] using (hrep p).2.1
    · intro hp
      apply Subtype.ext
      change T p = 0
      exact ((hrep p).2.2 0 (by simp)
        (by simpa only [map_zero, zero_mul, sub_zero] using hp)).symm
  let e : (MvPolynomial (Fin 4) ℂ ⧸ I) ≃ₗ[ℂ] Polynomial.degreeLT ℂ d :=
    (Submodule.quotEquivOfEq (I.restrictScalars ℂ) (LinearMap.ker F) hker.symm).trans
      (F.quotKerEquivOfSurjective hsurj)
  have he (p : MvPolynomial (Fin 4) ℂ) : e (Ideal.Quotient.mk I p) = F p := rfl
  let β : Module.Basis (Fin d) ℂ (MvPolynomial (Fin 4) ℂ ⧸ I) :=
    (Polynomial.degreeLT.basis ℂ d).map e.symm
  have hβ (i : Fin d) : β i =
      Ideal.Quotient.mk I ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q) := by
    apply e.injective
    change e (e.symm ((Polynomial.degreeLT.basis ℂ d) i)) = _
    rw [e.apply_symm_apply, he]
    apply Subtype.ext
    change ((Polynomial.degreeLT.basis ℂ d) i).val =
      T ((MvPolynomial.X (0 : Fin 4)) ^ i.val * q)
    have h := htime ((Polynomial.degreeLT.basis ℂ d) i)
    simpa only [E, Polynomial.degreeLT.basis_val, map_pow, Polynomial.aeval_X] using h.symm
  have hcoord (p : MvPolynomial (Fin 4) ℂ) (i : Fin d) :
      β.repr (Ideal.Quotient.mk I p) i = (T p).coeff i.val := by
    change ((Polynomial.degreeLT.basis ℂ d).repr (e (Ideal.Quotient.mk I p))) i = _
    rw [he, Polynomial.degreeLT.basis_repr]
    rfl
  refine ⟨β, ?_, hcoord, ?_, ?_⟩
  · intro i
    refine ⟨hβ i, (MvPolynomial.totalDegree_mul _ _).trans ?_⟩
    rw [MvPolynomial.totalDegree_X_pow]
    exact Nat.add_le_add (Nat.le_sub_one_of_lt i.isLt) le_rfl
  · intro p
    simpa only [hcoord, hβ] using (β.sum_repr (Ideal.Quotient.mk I p)).symm
  · simpa using Module.finrank_eq_card_basis β

