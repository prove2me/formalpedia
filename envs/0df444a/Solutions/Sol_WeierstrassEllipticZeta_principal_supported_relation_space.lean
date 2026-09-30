-- Prove2me | solution 1 for WeierstrassEllipticZeta.principal_supported_relation_space
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-13T03:38:13.583953+00:00
-- url     : https://prove2.me/submissions/88512d3e-31ba-419e-bd4c-d3273147c019

import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.RingTheory.Ideal.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Span.Basic

noncomputable section

theorem solution
    (K σ : Type*) [Field K] (p : MvPolynomial σ K) (hp : p ≠ 0)
    (S T : Finset (σ →₀ ℕ))
    (hsupport : ∀ d ∈ T, (p * MvPolynomial.monomial d 1).support ⊆ S) :
    ∃ R : Submodule K (MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))),
      Module.finrank K R = T.card ∧
      ∀ I : Ideal (MvPolynomial σ K), p ∈ I → ∀ q : R, q.val.val ∈ I := by
  classical
  let A := MvPolynomial.restrictSupport K (T : Set (σ →₀ ℕ))
  let B := MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))
  let M : MvPolynomial σ K →ₗ[K] MvPolynomial σ K := LinearMap.mulLeft K p
  have hmap : A.map M ≤ B := by
    change (MvPolynomial.restrictSupport K (T : Set (σ →₀ ℕ))).map M ≤ _
    rw [MvPolynomial.restrictSupport_eq_span, Submodule.map_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨q, ⟨d, hd, rfl⟩, rfl⟩
    change p * MvPolynomial.monomial d 1 ∈
      MvPolynomial.restrictSupport K (S : Set (σ →₀ ℕ))
    rw [MvPolynomial.mem_restrictSupport_iff, Finset.coe_subset]
    exact hsupport d hd
  let F : A →ₗ[K] B := LinearMap.codRestrict B (M.comp A.subtype)
    (fun q => hmap (Submodule.mem_map.mpr ⟨q.val, q.property, rfl⟩))
  have hinj : Function.Injective F := by
    intro q r h
    apply Subtype.ext
    apply mul_right_injective₀ hp
    exact congrArg Subtype.val h
  refine ⟨LinearMap.range F, ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinj]
    exact Module.finrank_eq_card_finset_basis
      (MvPolynomial.basisRestrictSupport K (T : Set (σ →₀ ℕ)))
  · intro I hpI q
    obtain ⟨r, hr⟩ := q.property
    rw [← congrArg Subtype.val hr]
    exact I.mul_mem_right r.val hpI
