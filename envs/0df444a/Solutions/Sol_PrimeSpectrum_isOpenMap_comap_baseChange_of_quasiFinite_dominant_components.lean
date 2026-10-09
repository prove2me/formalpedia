-- Prove2me | solution 1 for PrimeSpectrum.isOpenMap_comap_baseChange_of_quasiFinite_dominant_components
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T19:07:31.704008+00:00
-- url     : https://prove2.me/submissions/6a6fb80f-8fd5-4917-bcf2-7e86dcc4d0a4

import Theorems.Thm_PrimeSpectrum_isOpenMap_comap_baseChange_of_finite_domain
import Mathlib

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum.UniversalOpenness

/-- Transfer openness of structural maps along an algebra isomorphism. -/
theorem of_algEquiv
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra A C]
    (e : B ≃ₐ[A] C) (h : IsOpenMap (comap (algebraMap A C))) :
    IsOpenMap (comap (algebraMap A B)) := by
  rw [← e.symm.toAlgHom.comp_algebraMap, comap_comp]
  exact h.comp (isHomeomorph_comap_of_bijective e.symm.bijective).isOpenMap

/-- Localizing a factor preserves openness after a fixed affine base change. -/
theorem tensor_localization_open
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B]
    (h : IsOpenMap (comap (algebraMap B (B ⊗[A] R)))) (r : R) :
    IsOpenMap (comap (algebraMap B (B ⊗[A] Localization.Away r))) := by
  let e := IsLocalization.Away.tensorProductEquivTMulRight A B r (Localization.Away r)
  apply of_algEquiv e
  rw [IsScalarTower.algebraMap_eq B (B ⊗[A] R)
    (Localization.Away ((1 : B) ⊗ₜ[A] r)), comap_comp]
  exact h.comp (localization_away_isOpenEmbedding _ ((1 : B) ⊗ₜ[A] r)).isOpenMap

/-- A point of a tensor product lifts to the localized factor if its contraction
avoids the element being inverted. -/
theorem exists_tensor_localization_lift
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B]
    (q : PrimeSpectrum (B ⊗[A] R)) (r : R)
    (hr : r ∉ q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    ∃ q' : PrimeSpectrum (B ⊗[A] Localization.Away r),
      comap (Algebra.TensorProduct.map (AlgHom.id B B)
        (IsScalarTower.toAlgHom A R (Localization.Away r))).toRingHom q' = q := by
  let e := IsLocalization.Away.tensorProductEquivTMulRight A B r (Localization.Away r)
  have hq : q ∈ Set.range (comap (algebraMap (B ⊗[A] R)
      (Localization.Away ((1 : B) ⊗ₜ[A] r)))) := by
    rw [localization_away_comap_range _ ((1 : B) ⊗ₜ[A] r)]
    exact hr
  obtain ⟨q', hq'⟩ := hq
  refine ⟨comap e.toRingHom q', ?_⟩
  have he : e.toRingHom.comp
      (Algebra.TensorProduct.map (AlgHom.id B B)
        (IsScalarTower.toAlgHom A R (Localization.Away r))).toRingHom =
      algebraMap (B ⊗[A] R) (Localization.Away ((1 : B) ⊗ₜ[A] r)) := by
    apply RingHom.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b a => simp [e]
    | add x y hx hy => simp_all only [map_add]
  change comap (e.toRingHom.comp _) q' = q
  rw [he]
  exact hq'

universe uA uR uB

/-- Zariski's main theorem reduces universal openness for a quasi-finite domain
to universal openness for finite domain extensions. -/
theorem quasiFinite_domain_of_finite
    (A : Type uA) [CommRing A]
    (B : Type uB) [CommRing B] [Algebra A B]
    (hfinite : ∀ (D : Type uR) [CommRing D] [IsDomain D] [Algebra A D]
      [Module.Finite A D], Function.Injective (algebraMap A D) →
      IsOpenMap (comap (algebraMap B (B ⊗[A] D))))
    (R : Type uR) [CommRing R] [IsDomain R] [Algebra A R]
    [Algebra.FiniteType A R] [Algebra.QuasiFinite A R]
    (hinj : Function.Injective (algebraMap A R)) :
    IsOpenMap (comap (algebraMap B (B ⊗[A] R))) := by
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨q, hq, rfl⟩
  let p := q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  have hp : p.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨D, hD, r, hr, hbij⟩ :=
    Algebra.QuasiFiniteAt.exists_fg_and_exists_notMem_and_awayMap_bijective
      (R := A) p
  have : Module.Finite A D := Module.Finite.iff_fg.mpr hD
  have hDinj : Function.Injective (algebraMap A D) := by
    intro a b h
    exact hinj (congrArg Subtype.val h)
  have hDopen := tensor_localization_open (hfinite D hDinj) r
  let e := AlgEquiv.ofBijective (Localization.awayMapₐ D.val r) hbij
  let e' : (B ⊗[A] Localization.Away r) ≃ₐ[B]
      (B ⊗[A] Localization.Away r.val) :=
    Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B) e
  have hRopen := of_algEquiv e'.symm hDopen
  let f : (B ⊗[A] R) →ₐ[B] (B ⊗[A] Localization.Away r.val) :=
    Algebra.TensorProduct.map (AlgHom.id B B)
      (IsScalarTower.toAlgHom A R (Localization.Away r.val))
  obtain ⟨q', hq'⟩ := exists_tensor_localization_lift q r.val hr
  have hcomp : comap (algebraMap B (B ⊗[A] Localization.Away r.val)) =
      comap (algebraMap B (B ⊗[A] R)) ∘ comap f.toRingHom := by
    rw [← comap_comp]
    congr 1
    exact f.comp_algebraMap.symm
  refine ⟨comap (algebraMap B (B ⊗[A] Localization.Away r.val)) ''
      (comap f.toRingHom ⁻¹' U), ?_,
      hRopen _ (hU.preimage (continuous_comap f.toRingHom)), ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨comap f.toRingHom w, hw, congrFun hcomp w |>.symm⟩
  · refine ⟨q', ?_, ?_⟩
    · change comap f.toRingHom q' ∈ U
      rwa [hq']
    · rw [hcomp]
      change comap (algebraMap B (B ⊗[A] R)) (comap f.toRingHom q') = _
      rw [hq']

end PrimeSpectrum.UniversalOpenness
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology
noncomputable section

namespace PrimeSpectrum.UniversalOpenness

/-- Dominance of a component over a reduced base gives an injective structure
map into its reduced coordinate domain. -/
theorem component_quotient_injective
    {A R : Type*} [CommRing A] [IsReduced A] [CommRing R] [Algebra A R]
    (hdom : ∀ Z ∈ irreducibleComponents (PrimeSpectrum R),
      Dense (comap (algebraMap A R) '' Z))
    (p : Ideal R) (hp : p ∈ minimalPrimes R) :
    Function.Injective (algebraMap A (R ⧸ p)) := by
  have : p.IsPrime := hp.1.1
  have hZ : zeroLocus p ∈ irreducibleComponents (PrimeSpectrum R) := by
    rw [zeroLocus_ideal_mem_irreducibleComponents,
      Ideal.IsPrime.radical (inferInstance : p.IsPrime)]
    exact hp
  have hrange : Set.range (comap (algebraMap A (R ⧸ p))) =
      comap (algebraMap A R) '' zeroLocus p := by
    rw [IsScalarTower.algebraMap_eq A R (R ⧸ p), comap_comp, Set.range_comp]
    change _ '' Set.range (comap (Ideal.Quotient.mk p)) = _
    rw [range_comap_of_surjective _ _ (Ideal.Quotient.mk_surjective),
      Ideal.mk_ker]
  have hdense : DenseRange (comap (algebraMap A (R ⧸ p))) := by
    change Dense (Set.range _)
    rw [hrange]
    exact hdom _ hZ
  rw [RingHom.injective_iff_ker_eq_bot]
  apply le_antisymm _ bot_le
  simpa [nilradical_eq_zero] using
    (denseRange_comap_iff_ker_le_nilRadical _).mp hdense

/-- A prime of a tensor product lifts through the tensor product with a quotient
whenever its contraction contains the quotient ideal. No flatness is required. -/
theorem exists_tensor_quotient_lift
    {A R B : Type*} [CommRing A] [CommRing R] [CommRing B]
    [Algebra A R] [Algebra A B]
    (q : PrimeSpectrum (B ⊗[A] R)) (p : Ideal R)
    (hp : p ≤ q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom) :
    ∃ q' : PrimeSpectrum (B ⊗[A] (R ⧸ p)),
      comap (Algebra.TensorProduct.map (AlgHom.id B B)
        (Ideal.Quotient.mkₐ A p)).toRingHom q' = q := by
  let k := q.asIdeal.ResidueField
  let g : (B ⊗[A] R) →ₐ[B] k :=
    IsScalarTower.toAlgHom B (B ⊗[A] R) k
  let gR : R →ₐ[A] k := (g.restrictScalars A).comp Algebra.TensorProduct.includeRight
  have hkill : ∀ r ∈ p, gR r = 0 := by
    intro r hr
    exact Ideal.algebraMap_residueField_eq_zero.mpr (hp hr)
  let gQ : (R ⧸ p) →ₐ[A] k := Ideal.Quotient.liftₐ p gR hkill
  let e : (B ⊗[A] (R ⧸ p)) →ₐ[B] k :=
    Algebra.TensorProduct.lift (Algebra.ofId B k) gQ (fun _ _ => Commute.all _ _)
  let f : (B ⊗[A] R) →ₐ[B] (B ⊗[A] (R ⧸ p)) :=
    Algebra.TensorProduct.map (AlgHom.id B B) (Ideal.Quotient.mkₐ A p)
  have he : e.comp f = g := by
    apply Algebra.TensorProduct.ext'
    intro b r
    simp only [AlgHom.comp_apply, e, f, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, Algebra.TensorProduct.lift_tmul, gQ,
      Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.liftₐ_apply, Ideal.Quotient.lift_mk]
    change algebraMap B k b * algebraMap (B ⊗[A] R) k (1 ⊗ₜ[A] r) =
      algebraMap (B ⊗[A] R) k (b ⊗ₜ[A] r)
    rw [IsScalarTower.algebraMap_apply B (B ⊗[A] R) k, ← map_mul]
    simp
  let z : PrimeSpectrum k := ⟨⊥, inferInstance⟩
  refine ⟨comap e.toRingHom z, ?_⟩
  change comap (e.toRingHom.comp f.toRingHom) z = q
  change comap (e.comp f).toRingHom z = q
  rw [he]
  ext x
  exact Ideal.algebraMap_residueField_eq_zero

universe uA uR uB

/-- Openness after base change can be checked on all reduced irreducible
components, including for a nonreduced source. -/
theorem of_component_quotients
    (A : Type uA) [CommRing A] (R : Type uR) [CommRing R] [Algebra A R]
    (B : Type uB) [CommRing B] [Algebra A B]
    (hcomp : ∀ p ∈ minimalPrimes R,
      IsOpenMap (comap (algebraMap B (B ⊗[A] (R ⧸ p))))) :
    IsOpenMap (comap (algebraMap B (B ⊗[A] R))) := by
  intro U hU
  apply isOpen_iff_forall_mem_open.mpr
  rintro y ⟨q, hq, rfl⟩
  let Q := q.asIdeal.comap Algebra.TensorProduct.includeRight.toRingHom
  have : Q.IsPrime := Ideal.comap_isPrime _ _
  obtain ⟨p, hp, hpQ⟩ := Ideal.exists_minimalPrimes_le (I := ⊥) (J := Q) bot_le
  let f : (B ⊗[A] R) →ₐ[B] (B ⊗[A] (R ⧸ p)) :=
    Algebra.TensorProduct.map (AlgHom.id B B) (Ideal.Quotient.mkₐ A p)
  obtain ⟨q', hq'⟩ := exists_tensor_quotient_lift q p hpQ
  have he : comap (algebraMap B (B ⊗[A] (R ⧸ p))) =
      comap (algebraMap B (B ⊗[A] R)) ∘ comap f.toRingHom := by
    rw [← comap_comp]
    exact congrArg comap f.comp_algebraMap.symm
  refine ⟨comap (algebraMap B (B ⊗[A] (R ⧸ p))) ''
      (comap f.toRingHom ⁻¹' U), ?_,
      hcomp p hp _ (hU.preimage (continuous_comap f.toRingHom)), ?_⟩
  · rintro z ⟨w, hw, rfl⟩
    exact ⟨comap f.toRingHom w, hw, congrFun he w |>.symm⟩
  · refine ⟨q', ?_, ?_⟩
    · change comap f.toRingHom q' ∈ U
      rwa [hq']
    · rw [he]
      change comap (algebraMap B (B ⊗[A] R)) (comap f.toRingHom q') = _
      rw [hq']

/-- The full normal-base target reduces to the finite, injective domain case.
Normality and Noetherianity are needed only in that remaining finite case. -/
theorem quasiFinite_components_of_finite
    (A : Type uA) [CommRing A] [IsReduced A]
    (R : Type uR) [CommRing R] [Algebra A R]
    [Algebra.FiniteType A R] [Algebra.QuasiFinite A R]
    (hdom : ∀ Z ∈ irreducibleComponents (PrimeSpectrum R),
      Dense (comap (algebraMap A R) '' Z))
    (B : Type uB) [CommRing B] [Algebra A B]
    (hfinite : ∀ (D : Type uR) [CommRing D] [IsDomain D] [Algebra A D]
      [Module.Finite A D], Function.Injective (algebraMap A D) →
      IsOpenMap (comap (algebraMap B (B ⊗[A] D)))) :
    IsOpenMap (comap (algebraMap B (B ⊗[A] R))) := by
  apply of_component_quotients A R B
  intro p hp
  have : p.IsPrime := hp.1.1
  have : Algebra.QuasiFinite A (R ⧸ p) :=
    Algebra.QuasiFinite.of_surjective_algHom (Ideal.Quotient.mkₐ A p)
      (Ideal.Quotient.mkₐ_surjective A p)
  exact quasiFinite_domain_of_finite A B hfinite (R ⧸ p)
    (component_quotient_injective hdom p hp)

end PrimeSpectrum.UniversalOpenness
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped TensorProduct Topology

theorem solution
    (A : Type*) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [IsNoetherianRing A]
    (R : Type*) [CommRing R] [Algebra A R]
    [Algebra.FiniteType A R] [Algebra.QuasiFinite A R]
    (hdom : ∀ Z ∈ irreducibleComponents (PrimeSpectrum R),
      Dense (PrimeSpectrum.comap (algebraMap A R) '' Z))
    (B : Type*) [CommRing B] [Algebra A B] :
    IsOpenMap (PrimeSpectrum.comap (algebraMap B (B ⊗[A] R))) := by
  apply PrimeSpectrum.UniversalOpenness.quasiFinite_components_of_finite A R hdom B
  intro D _ _ _ _ hinj
  exact PrimeSpectrum.isOpenMap_comap_baseChange_of_finite_domain A D hinj B
