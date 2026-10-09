-- Prove2me | solution 1 for PrimeSpectrum.isOpenMap_comap_baseChange_of_finite_domain
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T19:30:08.136262+00:00
-- url     : https://prove2.me/submissions/929a1eb8-7c61-4378-81c4-eb05c2e2fd1d

import Mathlib

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum.FiniteDomainOpenness

attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem integrallyClosed_mvPolynomial
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    (σ : Type*) : IsIntegrallyClosed (MvPolynomial σ A) := by
  let K := FractionRing A
  have : IsIntegrallyClosed (MvPolynomial σ K) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  suffices IsIntegrallyClosedIn (MvPolynomial σ A) (MvPolynomial σ K) from
    .of_isIntegrallyClosed_of_isIntegrallyClosedIn _ (MvPolynomial σ K)
  refine isIntegrallyClosedIn_iff.mpr
    ⟨MvPolynomial.map_injective (algebraMap A K) (IsFractionRing.injective A K), ?_⟩
  intro p hp
  change p ∈ Set.range (MvPolynomial.map (algebraMap A K))
  rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
  intro c hc
  obtain ⟨d, _, hd⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  rw [hd]
  exact IsIntegrallyClosed.isIntegral_iff.mp
    (MvPolynomial.isIntegral_iff_isIntegral_coeff.mp hp d)

/-- Going down proves openness after adjoining an arbitrary set of variables. -/
theorem polynomial_open
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D)) (σ : Type*) :
    IsOpenMap (comap (algebraMap (MvPolynomial σ A) (MvPolynomial σ D))) := by
  let := integrallyClosed_mvPolynomial A σ
  let : FaithfulSMul (MvPolynomial σ A) (MvPolynomial σ D) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr
      (MvPolynomial.map_injective (algebraMap A D) hinj)
  let e := Algebra.IsPushout.equiv A (MvPolynomial σ A) D (MvPolynomial σ D)
  have : Module.Finite (MvPolynomial σ A) (MvPolynomial σ D) :=
    Module.Finite.equiv e.toLinearEquiv
  have : Algebra.FinitePresentation A D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FinitePresentation (MvPolynomial σ A) (MvPolynomial σ D) :=
    Algebra.FinitePresentation.equiv e
  exact isOpenMap_comap_of_hasGoingDown_of_finitePresentation

end PrimeSpectrum.FiniteDomainOpenness
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum.FiniteDomainOpenness

section Quotient

variable (P B T C : Type*) [CommRing P] [CommRing B] [CommRing T] [CommRing C]
  [Algebra P B] [Algebra P T] [Algebra P C] [Algebra B C] [Algebra T C]
  [IsScalarTower P B C] [IsScalarTower P T C] [Algebra.IsPushout P B T C]

/-- Compatible primes lift in a pushout along a surjective base homomorphism. -/
theorem quotient_prime_lift
    (hsurj : Function.Surjective (algebraMap P B))
    (b : PrimeSpectrum B) (t : PrimeSpectrum T)
    (heq : comap (algebraMap P T) t = comap (algebraMap P B) b) :
    ∃ c : PrimeSpectrum C,
      comap (algebraMap B C) c = b ∧ comap (algebraMap T C) c = t := by
  let K := t.asIdeal.ResidueField
  have hker : RingHom.ker (algebraMap P B) ≤ RingHom.ker (algebraMap P K) := by
    intro x hx
    rw [RingHom.mem_ker, IsScalarTower.algebraMap_apply P T K,
      Ideal.algebraMap_residueField_eq_zero]
    change x ∈ (comap (algebraMap P T) t).asIdeal
    rw [heq]
    change algebraMap P B x ∈ b.asIdeal
    rw [RingHom.mem_ker.mp hx]
    exact b.asIdeal.zero_mem
  let g : B →ₐ[P] K := AlgHom.liftOfSurjective (Algebra.ofId P B)
    hsurj (Algebra.ofId P K) hker
  let h : T →ₐ[P] K := IsScalarTower.toAlgHom P T K
  let F : C →ₐ[P] K := Algebra.pushoutDesc C g h (fun _ _ => mul_comm _ _)
  let c : PrimeSpectrum C := comap F.toRingHom ⊥
  have hct : comap (algebraMap T C) c = t := by
    ext x
    change F (algebraMap T C x) = 0 ↔ x ∈ t.asIdeal
    rw [Algebra.pushoutDesc_right]
    exact Ideal.algebraMap_residueField_eq_zero
  refine ⟨c, ?_, hct⟩
  apply comap_injective_of_surjective (algebraMap P B) hsurj
  rw [← comap_comp_apply, ← IsScalarTower.algebraMap_eq P B C,
    IsScalarTower.algebraMap_eq P T C, comap_comp_apply, hct]
  exact heq

/-- The other arrow in this pushout is also surjective. -/
theorem quotient_pushout_surjective
    (hsurj : Function.Surjective (algebraMap P B)) :
    Function.Surjective (algebraMap T C) := by
  let e := Algebra.IsPushout.equiv P B T C
  intro c
  obtain ⟨x, rfl⟩ := e.surjective c
  obtain ⟨t, rfl⟩ := Algebra.TensorProduct.includeRight_surjective
    (R := P) (S := B) (T := T) hsurj x
  exact ⟨t, by simp [e, Algebra.IsPushout.equiv_tmul]⟩

/-- An open affine map remains open after a quotient of its base ring. -/
theorem open_quotient_baseChange
    (hsurj : Function.Surjective (algebraMap P B))
    (hopen : IsOpenMap (comap (algebraMap P T))) :
    IsOpenMap (comap (algebraMap B C)) := by
  rw [isBasis_basic_opens.isOpenMap_iff]
  rintro _ ⟨_, ⟨c, rfl⟩, rfl⟩
  obtain ⟨t, rfl⟩ := quotient_pushout_surjective P B T C hsurj c
  have himage :
      comap (algebraMap B C) '' (basicOpen (algebraMap T C t) : Set (PrimeSpectrum C)) =
      comap (algebraMap P B) ⁻¹'
        (comap (algebraMap P T) '' (basicOpen t : Set (PrimeSpectrum T))) := by
    ext b
    constructor
    · rintro ⟨c, hc, rfl⟩
      refine ⟨comap (algebraMap T C) c, hc, ?_⟩
      rw [← comap_comp_apply, ← comap_comp_apply,
        ← IsScalarTower.algebraMap_eq P T C, ← IsScalarTower.algebraMap_eq P B C]
    · rintro ⟨t', ht', heq⟩
      obtain ⟨c, hcb, hct⟩ := quotient_prime_lift P B T C hsurj b t' heq
      refine ⟨c, ?_, hcb⟩
      change comap (algebraMap T C) c ∈ basicOpen t
      rwa [hct]
  rw [himage]
  exact (hopen _ (basicOpen t).isOpen).preimage (continuous_comap _)

end Quotient

end PrimeSpectrum.FiniteDomainOpenness
end

end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum.FiniteDomainOpenness

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial presentation and quotient descent give arbitrary base change. -/
theorem universally_open
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (B : Type*) [CommRing B] [Algebra A B] :
    IsOpenMap (comap (algebraMap B (B ⊗[A] D))) := by
  let P := MvPolynomial B A
  let e0 : P →ₐ[A] B := MvPolynomial.aeval (fun b : B => b)
  let : Algebra P B := e0.toAlgebra
  have : IsScalarTower A P B := .of_algebraMap_eq' e0.comp_algebraMap.symm
  have hsurj : Function.Surjective (algebraMap P B) := by
    intro b
    refine ⟨MvPolynomial.X b, ?_⟩
    change e0 (MvPolynomial.X b) = b
    exact MvPolynomial.aeval_X _ _
  let f : P ⊗[A] D →ₐ[A] B ⊗[A] D :=
    Algebra.TensorProduct.map e0 (AlgHom.id A D)
  let : Algebra (P ⊗[A] D) (B ⊗[A] D) := f.toAlgebra
  have : IsScalarTower P (P ⊗[A] D) (B ⊗[A] D) := by
    apply IsScalarTower.of_algebraMap_eq' (R := P) (S := P ⊗[A] D)
    apply RingHom.ext
    intro p
    change e0 p ⊗ₜ[A] (1 : D) = f (p ⊗ₜ[A] (1 : D))
    simp [f]
  have : Algebra.IsPushout P B (P ⊗[A] D) (B ⊗[A] D) := by
    apply Algebra.IsPushout.tensorProduct_tensorProduct A D P B
    ext d
    simp [RingHom.algebraMap_toAlgebra, f]
  apply open_quotient_baseChange P B (P ⊗[A] D) (B ⊗[A] D) hsurj
  let e := Algebra.IsPushout.equiv A P D (MvPolynomial B D)
  rw [← e.symm.toAlgHom.comp_algebraMap, comap_comp]
  exact (polynomial_open A D hinj B).comp
    (isHomeomorph_comap_of_bijective e.symm.bijective).isOpenMap

end PrimeSpectrum.FiniteDomainOpenness
end

end

set_option autoImplicit false
open scoped TensorProduct Topology

theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (D : Type*) [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (B : Type*) [CommRing B] [Algebra A B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] D))) := by
  exact PrimeSpectrum.FiniteDomainOpenness.universally_open A D hinj B
