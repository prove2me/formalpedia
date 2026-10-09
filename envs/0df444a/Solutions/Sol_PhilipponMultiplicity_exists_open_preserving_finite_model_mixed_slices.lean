-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_finite_model_mixed_slices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-08T03:58:02.27303+00:00
-- url     : https://prove2.me/submissions/f27e15f4-b426-46b6-b442-d3b8d47e86ad

import Theorems.Thm_PhilipponMultiplicity_mixed_finite_model_domain_and_dominance
import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_open_mixed_slices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Definitions.Def_PhilipponMultiplicity_UniversalMixedSlices
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped Topology
noncomputable section

namespace PhilipponMultiplicity.OpenMixedModel

/-- A finite domain over a normal Noetherian ring has an open spectrum map,
provided that the structural homomorphism is injective. -/
theorem finite_domain_isOpenMap
    {C D : Type*} [CommRing C] [CommRing D] [Algebra C D]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [IsDomain D]
    [Module.Finite C D] (hinj : Function.Injective (algebraMap C D)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap C D)) := by
  let : FaithfulSMul C D := (faithfulSMul_iff_algebraMap_injective C D).mpr hinj
  let : Algebra.FinitePresentation C D :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  exact PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation

/-- Openness transfers from the finite model to the principal neighbourhood
where that model agrees with the original algebra. -/
theorem localized_model_isOpenMap
    {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
    [IsNoetherianRing C] [IsIntegrallyClosed C] [IsDomain B]
    (hinj : Function.Injective (algebraMap C B))
    (D : Subalgebra C B) [Module.Finite C D] (r : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom r)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap C (Localization.Away r.val))) := by
  have hDinj : Function.Injective (algebraMap C D) := by
    intro x y h
    apply hinj
    exact congrArg Subtype.val h
  have hDopen := finite_domain_isOpenMap hDinj
  have hloc := (PrimeSpectrum.localization_away_isOpenEmbedding
    (Localization.Away r) r).isOpenMap
  have hiso := (PrimeSpectrum.isHomeomorph_comap_of_bijective hbij).isOpenMap
  have hcomp := hDopen.comp (hloc.comp hiso)
  have hmap :
      (Localization.awayMap D.val.toRingHom r).comp
        ((algebraMap D (Localization.Away r)).comp (algebraMap C D)) =
      algebraMap C (Localization.Away r.val) := by
    ext x
    change Localization.awayMapₐ D.val r
      (algebraMap C (Localization.Away r) x) = _
    exact (Localization.awayMapₐ D.val r).commutes x
  rw [← hmap, PrimeSpectrum.comap_comp, PrimeSpectrum.comap_comp]
  exact hcomp

/-- The same principal neighbourhood remains quasi-finite over the coefficient
ring. Finiteness is used before localization, where it is actually available. -/
theorem localized_model_quasiFinite
    {C B : Type*} [CommRing C] [CommRing B] [Algebra C B]
    (D : Subalgebra C B) [Module.Finite C D] (r : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom r)) :
    Algebra.QuasiFinite C (Localization.Away r.val) := by
  exact Algebra.QuasiFinite.of_surjective_algHom (Localization.awayMapₐ D.val r) hbij.2

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- Polynomial coefficient spaces are normal and Noetherian, so the preceding
criterion applies to the mixed incidence algebras. -/
theorem mixed_model_isOpenMap
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (W : Set M.Point)
    (l : List M.FactorIndex)
    (b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1))
    (H : M.CoordinateRing)
    (hdom : IsDomain (MixedFamily.CoordinateRing M W l b H))
    (hinj : Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
      (MixedFamily.CoordinateRing M W l b H)))
    (D : Subalgebra (MixedFamily.ParameterRing M l)
      (MixedFamily.CoordinateRing M W l b H))
    (hD : Module.Finite (MixedFamily.ParameterRing M l) D) (r : D)
    (hbij : Function.Bijective (Localization.awayMap D.val.toRingHom r)) :
    IsOpenMap (PrimeSpectrum.comap (algebraMap (MixedFamily.ParameterRing M l)
      (Localization.Away r.val))) ∧
    Algebra.QuasiFinite (MixedFamily.ParameterRing M l) (Localization.Away r.val) := by
  let := hdom
  let := hD
  let : IsNoetherianRing (MixedFamily.ParameterRing M l) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial (Fin l.length × M.Variable) K))
  let : IsIntegrallyClosed (MixedFamily.ParameterRing M l) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  constructor
  · exact localized_model_isOpenMap (C := MixedFamily.ParameterRing M l)
      (B := MixedFamily.CoordinateRing M W l b H) hinj D r hbij
  · exact localized_model_quasiFinite D r hbij

end PhilipponMultiplicity.OpenMixedModel
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section
attribute [local instance] MvPolynomial.algebraMvPolynomial

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem finite_model_persistence_of_open_charts
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hdominance : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      ∀ H : M.CoordinateRing,
      ∀ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
        Module.Finite (MixedFamily.ParameterRing M l) D →
        ∀ r : D, r.val ≠ 0 →
          Function.Bijective (Localization.awayMap D.val.toRingHom r) →
          IsDomain (MixedFamily.CoordinateRing M W l b H) ∧
          Function.Injective (algebraMap (MixedFamily.ParameterRing M l)
            (MixedFamily.CoordinateRing M W l b H)))
    (hpersistence : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ f : MixedFamily.CoordinateRing M W l b H,
                e f ≠ 0 ∧
                IsOpenMap (PrimeSpectrum.comap (algebraMap (MixedFamily.ParameterRing M l)
                  (Localization.Away f))) ∧
                Algebra.QuasiFinite (MixedFamily.ParameterRing M l) (Localization.Away f)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0})) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
                Module.Finite (MixedFamily.ParameterRing M l) D ∧ ∃ r : D,
                  e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  intro M W hW hirr α hα hdim l hl c₀ S hS hSZ hfinite
  apply hpersistence M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep,H,a,ha,e,hev,hec,D,hD,r,hr,hbij⟩ := hfinite x hx
  have hr0 : r.val ≠ 0 := by
    intro hz
    apply hr
    rw [hz, map_zero]
  obtain ⟨hdom,hinj⟩ := hdominance M W hW hirr α hα hdim l hl b H D hD r hr0 hbij
  obtain ⟨hopen,hquasi⟩ := OpenMixedModel.mixed_model_isOpenMap
    M W l b H hdom hinj D hD r hbij
  exact ⟨b,v,hb,hrep,H,a,ha,e,hev,hec,r.val,hr,hopen,hquasi⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology
attribute [local instance] MvPolynomial.algebraMvPolynomial

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
      ∀ c₀ : Fin l.length → M.Variable → K,
      ∀ S : Set M.Point, S.Finite →
      S ⊆ {x : M.Point | x ∈ W ∧
        ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c₀ j) x = 0} →
      (∀ x ∈ S,
        ∃ b : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
        ∃ v : M.Variable → K, (∀ i, v ⟨i,b i⟩ = 1) ∧
          (∀ i : M.FactorIndex, ∃ h : (fun j => v ⟨i,j⟩) ≠ 0,
            Projectivization.mk K (fun j => v ⟨i,j⟩) h = x i) ∧
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            ∃ e : MixedFamily.CoordinateRing M W l b H →ₐ[K] K,
              (∀ P : M.CoordinateRing,
                e (Ideal.Quotient.mk (MixedFamily.ideal M W l b H) (MixedFamily.fixed M l P)) =
                  MvPolynomial.eval v P) ∧
              (∀ P : MixedFamily.ParameterRing M l,
                e (algebraMap (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H) P) =
                  MvPolynomial.eval (Function.uncurry c₀) P) ∧
              ∃ D : Subalgebra (MixedFamily.ParameterRing M l) (MixedFamily.CoordinateRing M W l b H),
                Module.Finite (MixedFamily.ParameterRing M l) D ∧ ∃ r : D,
                  e r.val ≠ 0 ∧ Function.Bijective (Localization.awayMap D.val.toRingHom r)) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact finite_model_persistence_of_open_charts K hK
    (mixed_finite_model_domain_and_dominance K hK)
    (exists_open_preserving_open_mixed_slices K hK)
