-- Prove2me | solution 1 for WeierstrassEllipticZeta.monomial_reduction_stable_span
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T01:58:35.300023+00:00
-- url     : https://prove2.me/submissions/5adb65a4-a0de-40da-80f0-4d39da00721e

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fintype.EquivFin

noncomputable section

theorem solution
    (K σ : Type*) [Field K] (S : Finset (σ →₀ ℕ)) (hzero : 0 ∈ S)
    (r : σ → (σ →₀ ℕ) → MvPolynomial σ K)
    (hsupport : ∀ i : σ, ∀ d ∈ S, (r i d).support ⊆ S) :
    let J : Ideal (MvPolynomial σ K) := Ideal.span
      {p | ∃ i : σ, ∃ d ∈ S, p = MvPolynomial.X i * MvPolynomial.monomial d 1 - r i d}
    ∃ v : Fin S.card → MvPolynomial σ K ⧸ J,
      (1 : MvPolynomial σ K ⧸ J) ∈ Submodule.span K (Set.range v) ∧
      ∀ i : σ, ∀ j : Fin S.card,
        Ideal.Quotient.mk J (MvPolynomial.X i) * v j ∈ Submodule.span K (Set.range v) := by
  classical
  let J : Ideal (MvPolynomial σ K) := Ideal.span
    {p | ∃ i : σ, ∃ d ∈ S, p = MvPolynomial.X i * MvPolynomial.monomial d 1 - r i d}
  let q : MvPolynomial σ K →ₐ[K] MvPolynomial σ K ⧸ J := Ideal.Quotient.mkₐ K J
  let v : Fin S.card → MvPolynomial σ K ⧸ J :=
    fun j => q (MvPolynomial.monomial (S.equivFin.symm j).val 1)
  let V : Submodule K (MvPolynomial σ K ⧸ J) := Submodule.span K (Set.range v)
  have hmon (d : σ →₀ ℕ) (hd : d ∈ S) : q (MvPolynomial.monomial d 1) ∈ V := by
    refine Submodule.subset_span ⟨S.equivFin ⟨d, hd⟩, ?_⟩
    simp only [v, Equiv.symm_apply_apply]
  have hpoly (p : MvPolynomial σ K) (hp : p.support ⊆ S) : q p ∈ V := by
    rw [p.as_sum, map_sum]
    apply V.sum_mem
    intro d hd
    simpa only [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      using V.smul_mem (p.coeff d) (hmon d (hp hd))
  refine ⟨v, ?_, ?_⟩
  · simpa only [MvPolynomial.monomial_zero', map_one] using hmon 0 hzero
  · intro i j
    let d := S.equivFin.symm j
    have hrel : MvPolynomial.X i * MvPolynomial.monomial d.val 1 - r i d.val ∈ J :=
      Ideal.subset_span ⟨i, d.val, d.property, rfl⟩
    have heq : q (MvPolynomial.X i * MvPolynomial.monomial d.val 1) = q (r i d.val) :=
      Ideal.Quotient.eq.mpr hrel
    change q (MvPolynomial.X i) * q (MvPolynomial.monomial d.val 1) ∈ V
    rw [← map_mul, heq]
    exact hpoly (r i d.val) (hsupport i d.val d.property)
