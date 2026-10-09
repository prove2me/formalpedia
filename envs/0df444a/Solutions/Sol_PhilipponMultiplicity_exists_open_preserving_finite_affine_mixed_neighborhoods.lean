-- Prove2me | solution 1 for PhilipponMultiplicity.exists_open_preserving_finite_affine_mixed_neighborhoods
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-07T14:49:35.574228+00:00
-- url     : https://prove2.me/submissions/dca98bae-6402-4ca3-8990-5764e6f01a72

import Theorems.Thm_PhilipponMultiplicity_exists_open_preserving_finite_polynomial_mixed_slices
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib


section

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false
noncomputable section

namespace PhilipponMultiplicity.FinitePolynomialSlice
open Polynomial

/-- Adjoining the inverse of `h` presents the localized equation algebra as
a polynomial quotient. The original ideal is retained, without taking radicals. -/
def quotientAwayEquiv {R : Type*} [CommRing R] (I : Ideal R) (h : R) :
    ((Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h))) ≃ₐ[R]
      (Polynomial R ⧸ (I.map C ⊔ Ideal.span {C h * X - 1})) := by
  let J : Ideal (Polynomial R) := Ideal.span {C h * X - 1}
  let e := Localization.awayEquivAdjoin h
  have he : (I.map C).map (Ideal.Quotient.mk J) =
      (I.map (algebraMap R (Localization.Away h))).map e.toRingEquiv.toRingHom := by
    rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext r
    exact (e.commutes r).symm
  exact (Ideal.quotientEquivAlg _ _ e he).trans
    ((DoubleQuot.quotQuotEquivQuotSupₐ R J (I.map C)).trans
      (Ideal.quotientEquivAlgOfEq R (sup_comm J (I.map C))))

/-- Finiteness of the actual localized quotient transfers to its polynomial
presentation, over any commutative coefficient ring. -/
theorem finite_polynomial_quotient {K R : Type*} [CommRing K] [CommRing R]
    [Algebra K R] (I : Ideal R) (h : R)
    (hfinite : Module.Finite K
      ((Localization.Away h) ⧸ I.map (algebraMap R (Localization.Away h)))) :
    Module.Finite K (Polynomial R ⧸ (I.map C ⊔ Ideal.span {C h * X - 1})) := by
  letI := hfinite
  exact Module.Finite.equiv ((quotientAwayEquiv I h).restrictScalars K).toLinearEquiv

/-- The affine presentation commutes with specialization of coefficients. -/
theorem map_graph_ideal {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (h : R) :
    (I.map C ⊔ Ideal.span {C h * X - 1}).map (Polynomial.mapRingHom f) =
      (I.map f).map C ⊔ Ideal.span {C (f h) * X - 1} := by
  rw [Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  congr 1
  · rw [Ideal.map_map, Ideal.map_map]
    congr 1
    ext r
    simp
  · simp

/-- A point of the polynomial presentation is exactly a point of the original
equations together with an inverse value for the denominator. -/
theorem graph_ideal_le_ker_iff {R K : Type*} [CommRing R] [CommRing K]
    (f : R →+* K) (I : Ideal R) (h : R) (a : K) :
    (I.map C ⊔ Ideal.span {C h * X - 1}) ≤
      RingHom.ker (Polynomial.eval₂RingHom f a) ↔
        I ≤ RingHom.ker f ∧ f h * a = 1 := by
  rw [sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le]
  constructor
  · rintro ⟨hI, hrel⟩
    refine ⟨?_, ?_⟩
    · intro r hr
      simpa using hI hr
    · have hr := hrel (Set.mem_singleton (C h * X - 1))
      simpa [RingHom.mem_ker, sub_eq_zero] using hr
  · rintro ⟨hI, hrel⟩
    constructor
    · intro r hr
      simpa using hI hr
    · rintro P rfl
      simpa [RingHom.mem_ker, sub_eq_zero] using hrel

/-- At a rational affine point where the denominator is nonzero, its inverse
gives the extra coordinate of the finite polynomial presentation. -/
theorem finite_graph_at_point {K σ : Type*} [Field K]
    (v : σ → K) (I : Ideal (MvPolynomial σ K)) (H : MvPolynomial σ K)
    (hH : MvPolynomial.eval v H ≠ 0)
    (hfinite : Module.Finite K ((Localization.Away H) ⧸
      I.map (algebraMap (MvPolynomial σ K) (Localization.Away H)))) :
    ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
      Module.Finite K (Polynomial (MvPolynomial σ K) ⧸
        (I.map C ⊔ Ideal.span {C H * X - 1})) := by
  exact ⟨(MvPolynomial.eval v H)⁻¹, mul_inv_cancel₀ hH,
    finite_polynomial_quotient I H hfinite⟩

end PhilipponMultiplicity.FinitePolynomialSlice
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem finite_affine_persistence_of_finite_polynomial_slices
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
          ∃ H : M.CoordinateRing, ∃ a : K, MvPolynomial.eval v H * a = 1 ∧
            Module.Finite K ((Polynomial M.CoordinateRing) ⧸
              (((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
                Ideal.span (Set.range (fun i : M.FactorIndex =>
                  (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))).map
                  Polynomial.C ⊔ Ideal.span {Polynomial.C H * Polynomial.X - 1}))) →
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
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  intro M W hW hirr α hα hdim l hl c₀ S hS hSZ hfinite
  apply hgeometry M W hW hirr α hα hdim l hl c₀ S hS hSZ
  intro x hx
  obtain ⟨b,v,hb,hrep,H,hH,hQ⟩ := hfinite x hx
  obtain ⟨a,ha,hQH⟩ := FinitePolynomialSlice.finite_graph_at_point v
    ((MixedFlag.ideal M (M.vanishingIdeal W) l c₀ l.length) ⊔
      Ideal.span (Set.range (fun i : M.FactorIndex =>
        (MvPolynomial.X (⟨i,b i⟩ : M.Variable) : M.CoordinateRing) - 1))) H hH hQ
  exact ⟨b,v,hb,hrep,H,a,ha,hQH⟩

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
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}) := by
  exact finite_affine_persistence_of_finite_polynomial_slices K hK
    (exists_open_preserving_finite_polynomial_mixed_slices K hK)
