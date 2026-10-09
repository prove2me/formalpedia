-- Prove2me | solution 1 for PhilipponMultiplicity.exists_mixed_cut_flag_with_point_local_conditions
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-02T10:13:12.780964+00:00
-- url     : https://prove2.me/submissions/95eb6b99-6237-4118-9690-eae323ec072f

import Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_completed_local_conditions
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nullstellensatz

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PhilipponMultiplicity.CompletionDescent

section Faithful
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]

/-- Faithful flatness detects actual ideal membership, without taking radicals. -/
theorem mem_extended_iff (I : Ideal R) (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔ x ∈ I := by
  change x ∈ (I.map (algebraMap R S)).comap (algebraMap R S) ↔ x ∈ I
  rw [Ideal.comap_map_eq_self_of_faithfullyFlat]

/-- Injectivity of multiplication on the extended quotient descends. -/
theorem mul_regular_descends (I : Ideal R) (p : R)
    (h : ∀ q : S, algebraMap R S p * q ∈ I.map (algebraMap R S) →
      q ∈ I.map (algebraMap R S)) :
    ∀ q : R, p * q ∈ I → q ∈ I := by
  intro q hq
  apply (mem_extended_iff (S := S) I q).mp
  apply h (algebraMap R S q)
  rw [← map_mul]
  exact (mem_extended_iff (S := S) I (p * q)).mpr hq

/-- Reducedness of the extended quotient descends by contraction of its ideal. -/
theorem radical_descends (I : Ideal R)
    (h : (I.map (algebraMap R S)).IsRadical) : I.IsRadical := by
  have hc := h.comap (algebraMap R S)
  rwa [Ideal.comap_map_eq_self_of_faithfullyFlat] at hc

end Faithful

section Completion
variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

/-- Completion at the maximal ideal is faithfully flat over a Noetherian local ring. -/
theorem completion_faithfullyFlat :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

variable {A : Type*} [CommRing A]

/-- For an ideal extended from another ring, multiplication injectivity in the
completion gives injectivity in the original local ring. -/
theorem mul_regular_of_completed_map (f : A →+* R) (I : Ideal A) (p : A)
    (h : let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
      let c := (algebraMap R C).comp f
      ∀ q : C, c p * q ∈ I.map c → q ∈ I.map c) :
    ∀ q : R, f p * q ∈ I.map f → q ∈ I.map f := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : Module.FaithfullyFlat R C := completion_faithfullyFlat R
  apply mul_regular_descends (S := C) (I.map f) (f p)
  simpa only [Ideal.map_map, RingHom.comp_apply] using h

/-- Radicality of the completed extension descends to the actual local ideal. -/
theorem radical_of_completed_map (f : A →+* R) (I : Ideal A)
    (h : let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
      (I.map ((algebraMap R C).comp f)).IsRadical) :
    (I.map f).IsRadical := by
  let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
  let : Module.FaithfullyFlat R C := completion_faithfullyFlat R
  apply radical_descends (S := C)
  simpa only [Ideal.map_map] using h

end Completion

end PhilipponMultiplicity.CompletionDescent
end

section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem point_local_cut_flag_of_completed_local_conditions
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hinput : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
              let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
              let f := (algebraMap R C).comp (algebraMap M.CoordinateRing R)
              ∀ Q : C, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
            let C := AdicCompletion (IsLocalRing.maximalIdeal R) R
            let f := (algebraMap R C).comp (algebraMap M.CoordinateRing R)
            ((J l.length).map f).IsRadical)) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let f := algebraMap M.CoordinateRing
                (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, hstep, hgeometry,
    hfinal⟩ := hinput M W hW hirr α hα hdim B hB hBW hnonempty
  refine ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, ?_, hgeometry, ?_⟩
  · intro k hk
    refine ⟨(hstep k hk).1, (hstep k hk).2.1, ?_⟩
    intro v hblocks hv
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    exact CompletionDescent.mul_regular_of_completed_map R
      (algebraMap M.CoordinateRing R) (J k) (P k) ((hstep k hk).2.2 v hblocks hv)
  · intro v hblocks hv
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    exact CompletionDescent.radical_of_completed_map R
      (algebraMap M.CoordinateRing R) (J l.length) (hfinal v hblocks hv)

end PhilipponMultiplicity
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∃ L : ∀ i : M.FactorIndex, Submodule K (Fin (M.ambientDimension i + 1) → K),
        (∀ i, Module.finrank K (L i) + α i = M.ambientDimension i + 1) ∧
        (linearSlice M W L).Finite ∧ Disjoint (linearSlice M W L) B ∧
        ∃ (l : List M.FactorIndex) (P : ℕ → M.CoordinateRing)
          (J : ℕ → Ideal M.CoordinateRing),
          (∀ i, l.count i = α i) ∧ J 0 = M.vanishingIdeal W ∧
          (∀ k (hk : k < l.length),
            M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧
            J (k+1) = J k ⊔ Ideal.span {P k} ∧
            ∀ v : M.Variable → K,
              (∀ i : M.FactorIndex,
                (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
              (∀ Q ∈ J k, MvPolynomial.eval v Q = 0) →
              let f := algebraMap M.CoordinateRing
                (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))).IsRadical) := by
  exact point_local_cut_flag_of_completed_local_conditions K hK
    (exists_mixed_cut_flag_with_completed_local_conditions K hK)
