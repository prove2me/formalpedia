-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_finite_local_mixed_slices
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T13:34:25.3028+00:00
-- url     : https://prove2.me/submissions/f939e50f-9fb1-4024-91dd-d47263f2a5c6

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_affine_mixed_neighborhoods
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 250000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.FiniteAffineNeighborhood

/-- A finite localized equation algebra over a Noetherian base is already finite
on a principal open neighborhood. The ideal is retained without radicalization. -/
theorem exists_finite_away_of_finite_quotient
    {K R L : Type*} [CommRing K] [CommRing R] [CommRing L]
    [Algebra K R] [Algebra R L] [Algebra K L] [IsScalarTower K R L]
    [IsNoetherianRing R] (S : Submonoid R) [IsLocalization S L]
    (I : Ideal R) [Module.Finite K (L ⧸ I.map (algebraMap R L))] :
    ∃ h ∈ S, Module.Finite K ((Localization.Away h) ⧸
      I.map (algebraMap R (Localization.Away h))) := by
  let Q := L ⧸ I.map (algebraMap R L)
  let f := (IsScalarTower.toAlgHom R (R ⧸ I) Q).toLinearMap
  haveI : Module.Finite R Q := Module.Finite.of_restrictScalars_finite K R Q
  haveI : Module.FinitePresentation R Q := Module.finitePresentation_of_finite R Q
  obtain ⟨h, hh, hf⟩ :=
    IsLocalizedModule.exists_isLocalizedModule_powers_of_finitePresentation S f
  letI : IsLocalizedModule.Away h f := hf
  let Qh := (Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h))
  let g := (IsScalarTower.toAlgHom R (R ⧸ I) Qh).toLinearMap
  let e := IsLocalizedModule.linearEquiv (Submonoid.powers h) f g
  exact ⟨h, hh, Module.Finite.equiv (e.restrictScalars K)⟩

/-- Finiteness at an affine rational point extends to an explicitly specified
principal open containing that point, for the same equations. -/
theorem exists_finite_polynomial_neighborhood
    {K σ : Type*} [Field K] [Finite σ] (v : σ → K)
    (I : Ideal (MvPolynomial σ K))
    (hfinite : Module.Finite K
      ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
        I.map (algebraMap (MvPolynomial σ K)
          (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) :
    ∃ H : MvPolynomial σ K, MvPolynomial.eval v H ≠ 0 ∧
      Module.Finite K ((Localization.Away H) ⧸
        I.map (algebraMap (MvPolynomial σ K) (Localization.Away H))) := by
  letI := hfinite
  obtain ⟨H, hH, hQ⟩ := exists_finite_away_of_finite_quotient
    (K := K) (L := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
    (MvPolynomial.vanishingIdeal K {v}).primeCompl I
  exact ⟨H, fun h => hH ((MvPolynomial.mem_vanishingIdeal_singleton_iff v H).mpr h), hQ⟩

end PhilipponMultiplicity.FiniteAffineNeighborhood
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem finite_local_persistence_of_finite_affine_neighborhoods
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
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
          ∃ H : M.CoordinateRing, MvPolynomial.eval v H ≠ 0 ∧
            Module.Finite K ((Localization.Away H) ⧸
              ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  (algebraMap M.CoordinateRing (Localization.Away H)))) →
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
          Module.Finite K ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
            ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
              Ideal.span (Set.range (fun i : M.FactorIndex =>
                (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                (algebraMap M.CoordinateRing
                  (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) →
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
  apply hgeometry M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep,hQ⟩ := hfinite x hx
  obtain ⟨H,hH,hQH⟩ := FiniteAffineNeighborhood.exists_finite_polynomial_neighborhood v
    ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
      Ideal.span (Set.range (fun i : M.FactorIndex =>
        (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))) hQ
  exact ⟨b,v,hb,hrep,H,hH,hQH⟩

end PhilipponMultiplicity
end

end

set_option autoImplicit false
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

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
          Module.Finite K ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
            ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
              Ideal.span (Set.range (fun i : M.FactorIndex =>
                (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                (algebraMap M.CoordinateRing
                  (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) →
        ∃ U : Set (PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)),
          IsOpen U ∧
          (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c₀}, inferInstance⟩ :
            PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U ∧
          ∀ c : Fin l.length → M.Variable → K,
            (⟨MvPolynomial.vanishingIdeal K {Function.uncurry c}, inferInstance⟩ :
              PrimeSpectrum (MvPolynomial (Fin l.length × M.Variable) K)) ∈ U →
            Nonempty (S ↪ {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact finite_local_persistence_of_finite_affine_neighborhoods K hK
    (exists_open_preserving_finite_affine_mixed_neighborhoods K hK)
