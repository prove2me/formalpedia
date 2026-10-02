-- Prove2me | solution 1 for PhilipponMultiplicity.exists_mixed_cut_flag_reduced_on_relevant_locus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T17:03:03.5707+00:00
-- url     : https://prove2.me/submissions/d870f94b-a39d-42c0-a663-e2e4b3e9c4f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_mixed_cut_flag_with_coordinate_local_conditions
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_PrimaryDecomposition_associatedPrimes_eq
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_exists_primaryDecomposition
import Mathlib.RingTheory.Lasker
import Mathlib.RingTheory.Localization.Ideal
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
set_option autoImplicit false
open scoped BigOperators Topology

section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem associatedPrimes_quotient_eq (I : Ideal R) :
    associatedPrimes R (R ⧸ I) = I.associatedPrimes := by
  have hc (f : R) : (⊥ : Submodule R (R ⧸ I)).colon {Ideal.Quotient.mk I f} = I.colon {f} := by
    ext x
    simp only [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]
    rfl
  ext q
  constructor
  · rintro ⟨hp, x, heq⟩
    obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact ⟨hp, f, heq.trans (congrArg Ideal.radical (hc f))⟩
  · rintro ⟨hp, f, heq⟩
    exact ⟨hp, Ideal.Quotient.mk I f, heq.trans (congrArg Ideal.radical (hc f).symm)⟩

end PhilipponMultiplicity.ComponentSelection
end
end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem blockWeight_apply (d : M.Variable →₀ ℕ) (i : M.FactorIndex) :
    (Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d) i =
      ∑ j : Fin (M.ambientDimension i + 1), d ⟨i, j⟩ := by
  classical
  rw [Finsupp.weight_eq_sum, Fintype.sum_sigma]
  change (∑ b : M.FactorIndex,
    ∑ j : Fin (M.ambientDimension b + 1),
      d ⟨b, j⟩ • Hilbert.blockWeight M.factorCount M.ambientDimension ⟨b, j⟩) i = _
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Hilbert.blockWeight,
    Pi.single_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Ne.symm hbi]
  · simp

theorem degreePiece_iff (P : M.CoordinateRing) (D : M.FactorIndex → ℕ) :
    P ∈ Hilbert.degreePiece K M.factorCount M.ambientDimension D ↔ M.IsHomogeneous P D := by
  change (∀ d, coeff d P ≠ 0 →
    Finsupp.weight (Hilbert.blockWeight M.factorCount M.ambientDimension) d = D) ↔ _
  simp only [← mem_support_iff]
  constructor
  · intro h d hd i
    exact (M.blockWeight_apply d i).symm.trans (congrFun (h d hd) i)
  · intro h d hd
    funext i
    rw [M.blockWeight_apply]
    exact h d hd i


end PhilipponMultiplicity.MultiProjectiveSpace
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem homogeneous_sup_span (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (P : M.CoordinateRing)
    (D : M.FactorIndex → ℕ) (hP : M.IsHomogeneous P D) :
    IsMultihomogeneousIdeal M (I ⊔ Ideal.span {P}) := by
  classical
  let w := blockWeight M.factorCount M.ambientDimension
  letI := weightedGradedAlgebra K w
  have hIg : I.IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    intro d f hf
    change ((MvPolynomial.decompose' K w f) d : M.CoordinateRing) ∈ I
    simpa only [GradedRing.proj_apply, MvPolynomial.decompose'_apply] using hI f hf d
  have hPg : (Ideal.span {P}).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro f hf
    have heq : f = P := Set.mem_singleton_iff.mp hf
    subst f
    exact ⟨D, (M.degreePiece_iff P D).mpr hP⟩
  intro f hf d
  exact weightedHomogeneousComponent_mem_of_mem K w (hIg.sup hPg) hf d


end PhilipponMultiplicity.Hilbert
end
end


section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators
open MvPolynomial
noncomputable section

namespace PhilipponMultiplicity
open SectionThree

theorem vanishingIdeal_multihomogeneous (K : Type*) [Field K]
    (M : MultiProjectiveSpace K) (S : Set M.Point) :
    IsMultihomogeneousIdeal M (M.vanishingIdeal S) := by
  classical
  let w := Hilbert.blockWeight M.factorCount M.ambientDimension
  letI := MvPolynomial.weightedGradedAlgebra K w
  have hh : (M.vanishingIdeal S).IsHomogeneous (weightedHomogeneousSubmodule K w) := by
    apply Ideal.homogeneous_span
    intro P hP
    obtain ⟨D, hD⟩ := hP.1
    refine ⟨D, ?_⟩
    intro e he
    funext i
    rw [M.blockWeight_apply]
    exact hD e (mem_support_iff.mpr he) i
  intro P hP d
  exact weightedHomogeneousComponent_mem_of_mem K w hh hP d


end PhilipponMultiplicity
end
end


section
namespace PhilipponMultiplicity.Hilbert
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)
theorem homogeneous_cut_chain (l : List M.FactorIndex)
    (J : ℕ → Ideal M.CoordinateRing) (P : ℕ → M.CoordinateRing)
    (hzero : IsMultihomogeneousIdeal M (J 0))
    (hstep : ∀ k (hk : k < l.length),
      M.IsHomogeneous (P k) (Pi.single l[k] 1) ∧ J (k+1) = J k ⊔ Ideal.span {P k}) :
    ∀ k ≤ l.length, IsMultihomogeneousIdeal M (J k) := by
  intro k
  induction k with
  | zero => exact fun _ => hzero
  | succ k ih =>
    intro hk
    obtain ⟨hP,hJ⟩ := hstep k (by omega)
    rw [hJ]
    exact homogeneous_sup_span M _ (ih (by omega)) _ _ hP


end PhilipponMultiplicity.Hilbert
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
noncomputable section

namespace PhilipponMultiplicity.LocalCutSupport
variable {R : Type*} [CommRing R]

/-- Reducedness in a principal localization propagates to any prime
localization where the chosen denominator is invertible. -/
theorem isRadical_atPrime_of_away (I : Ideal R) (s : R)
    (q : PrimeSpectrum R) (hs : s ∉ q.asIdeal)
    (hred : (I.map (algebraMap R (Localization.Away s))).IsRadical) :
    (I.map (algebraMap R (Localization.AtPrime q.asIdeal))).IsRadical := by
  let := q.isPrime
  apply Ideal.radical_eq_iff.mp
  apply le_antisymm ?_ Ideal.le_radical
  rw [← IsLocalization.map_radical q.asIdeal.primeCompl (Localization.AtPrime q.asIdeal)]
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  have hxa : algebraMap R (Localization.Away s) x ∈
      I.map (algebraMap R (Localization.Away s)) := by
    rw [← hred.radical]
    exact (I.map_radical_le _) (Ideal.mem_map_of_mem _ hx)
  obtain ⟨t,ht,htx⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s) (Localization.Away s) I x).mp hxa
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff t s).mp ht
  have hsn : s ^ n ∉ q.asIdeal := fun h => hs (q.isPrime.mem_of_pow_mem n h)
  have hu := IsLocalization.map_units (Localization.AtPrime q.asIdeal)
    (⟨s ^ n,hsn⟩ : q.asIdeal.primeCompl)
  have hm := Ideal.mem_map_of_mem
    (algebraMap R (Localization.AtPrime q.asIdeal)) htx
  rw [map_mul] at hm
  exact (Ideal.unit_mul_mem_iff_mem _ hu).mp hm

/-- An element acting injectively on a principal-localized quotient avoids
every associated prime at which that chart is defined. -/
theorem not_mem_associatedPrime_of_away_injective [IsNoetherianRing R]
    (I q : Ideal R) (hq : q ∈ associatedPrimes R (R ⧸ I))
    (s P : R) (hs : s ∉ q)
    (hinj : ∀ Q : Localization.Away s,
      algebraMap R (Localization.Away s) P * Q ∈
        I.map (algebraMap R (Localization.Away s)) →
      Q ∈ I.map (algebraMap R (Localization.Away s))) : P ∉ q := by
  have hassoc : I.IsAssociatedPrime q := by
    rw [ComponentSelection.associatedPrimes_quotient_eq] at hq
    exact hq
  obtain ⟨hprime,r,hr⟩ := Submodule.isAssociatedPrime_iff.mp hassoc
  intro hP
  have hPr : P * r ∈ I := by
    rw [hr,Submodule.mem_colon_singleton,smul_eq_mul] at hP
    exact hP
  have hm : algebraMap R (Localization.Away s) P *
      algebraMap R (Localization.Away s) r ∈
        I.map (algebraMap R (Localization.Away s)) := by
    rw [← map_mul]
    exact Ideal.mem_map_of_mem _ hPr
  obtain ⟨t,ht,htr⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers s) (Localization.Away s) I r).mp
      (hinj (algebraMap R (Localization.Away s) r) hm)
  obtain ⟨n,rfl⟩ := (Submonoid.mem_powers_iff t s).mp ht
  have hn : s ^ n ∈ q := by
    rw [hr,Submodule.mem_colon_singleton,smul_eq_mul]
    exact htr
  exact hs (hprime.mem_of_pow_mem n hn)

end PhilipponMultiplicity.LocalCutSupport

namespace PhilipponMultiplicity.MultiProjectiveSpace
open SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The products of one variable from each coordinate block cover every
relevant prime, including nonhomogeneous primes. -/
theorem exists_coordinate_product_not_mem (q : Ideal M.CoordinateRing)
    (hq : q.IsPrime)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    ∃ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      (∏ i, MvPolynomial.X (⟨i,j i⟩ : M.Variable)) ∉ q := by
  classical
  let := hq
  have hx (i : M.FactorIndex) : ∃ j : Fin (M.ambientDimension i + 1),
      MvPolynomial.X (⟨i,j⟩ : M.Variable) ∉ q := by
    by_contra! h
    apply hrel
    apply (iInf_le (Hilbert.blockIdeal K M.factorCount M.ambientDimension) i).trans
    rw [Hilbert.blockIdeal, Ideal.span_le]
    rintro _ ⟨j,rfl⟩
    exact h j
  choose j hj using hx
  refine ⟨j,?_⟩
  intro h
  obtain ⟨i,_,hi⟩ := Ideal.IsPrime.prod_mem_iff.mp h
  exact hj i hi

/-- It suffices to check reducedness on the finitely many coordinate
localizations of the multicone. -/
theorem isRadical_at_relevant_of_coordinate_localizations
    (I : Ideal M.CoordinateRing)
    (hred : ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      (I.map (algebraMap M.CoordinateRing
        (Localization.Away (∏ i, (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical)
    (q : PrimeSpectrum M.CoordinateRing)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal) :
    (I.map (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))).IsRadical := by
  obtain ⟨j,hj⟩ := M.exists_coordinate_product_not_mem q.asIdeal q.isPrime hrel
  exact LocalCutSupport.isRadical_atPrime_of_away I _ q hj (hred j)

/-- Injectivity on the coordinate localizations supplies a genuine minimal
homogeneous primary decomposition with all relevant radicals avoided.
Relevant embedded primes are included. -/
theorem exists_primary_avoidance_of_coordinate_injective
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (P : M.CoordinateRing)
    (hinj : ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
      let f := algebraMap M.CoordinateRing
        (Localization.Away (∏ i, (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
      ∀ Q, f P * Q ∈ I.map f → Q ∈ I.map f) :
    ∃ A : PrimaryDecomposition M I, ∀ a : Fin A.count,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component a).radical →
      P ∉ (A.component a).radical := by
  obtain ⟨A⟩ := exists_primaryDecomposition M I hI
  refine ⟨A,fun a ha => ?_⟩
  have hassoc : (A.component a).radical ∈
      associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) := by
    rw [PrimaryDecomposition.associatedPrimes_eq M I A]
    exact ⟨a,rfl⟩
  obtain ⟨j,hj⟩ := M.exists_coordinate_product_not_mem (A.component a).radical
    (Ideal.isPrime_radical (A.primary a)) ha
  exact LocalCutSupport.not_mem_associatedPrime_of_away_injective I _ hassoc _ P hj (hinj j)

end PhilipponMultiplicity.MultiProjectiveSpace

end
end


section

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

/-- Coordinate-local injectivity supplies primary-prime avoidance, and
coordinate-local reducedness supplies reducedness at every relevant prime. -/
theorem reduced_cut_flag_of_coordinate_local_conditions
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hchoice : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
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
            ∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
              let f := algebraMap M.CoordinateRing
                (Localization.Away (∏ i,
                  (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing)))
              ∀ Q, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ j : ∀ i : M.FactorIndex, Fin (M.ambientDimension i + 1),
            ((J l.length).map (algebraMap M.CoordinateRing
              (Localization.Away (∏ i,
                (MvPolynomial.X (⟨i,j i⟩ : M.Variable) : M.CoordinateRing))))).IsRadical)) :
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
            ∃ A : PrimaryDecomposition M (J k), ∀ j : Fin A.count,
              Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
              P k ∉ (A.component j).radical) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum M.CoordinateRing,
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
            ((J l.length).map
              (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))).IsRadical) := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,hfirst,hstep,hgeometry,hreduced⟩ :=
    hchoice M W hW hirr α hα hdim B hB hBW hnonempty
  have hhom := Hilbert.homogeneous_cut_chain M l J P
    (by rw [hfirst]; exact vanishingIdeal_multihomogeneous K M W)
    (fun k hk => ⟨(hstep k hk).1,(hstep k hk).2.1⟩)
  refine ⟨L,hL,hfinite,hdisjoint,l,P,J,hcount,hfirst,?_,hgeometry,?_⟩
  · intro k hk
    refine ⟨(hstep k hk).1,(hstep k hk).2.1,?_⟩
    exact M.exists_primary_avoidance_of_coordinate_injective
      (J k) (hhom k (Nat.le_of_lt hk)) (P k) (hstep k hk).2.2
  · intro q hq
    exact M.isRadical_at_relevant_of_coordinate_localizations
      (J l.length) hreduced q hq

end PhilipponMultiplicity
end
end

open PhilipponMultiplicity PhilipponMultiplicity.SectionThree PhilipponMultiplicity.SectionThreeSupport

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
            ∃ A : PrimaryDecomposition M (J k), ∀ j : Fin A.count,
              Hilbert.IsRelevant K M.factorCount M.ambientDimension (A.component j).radical →
              P k ∉ (A.component j).radical) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum M.CoordinateRing,
            Hilbert.IsRelevant K M.factorCount M.ambientDimension q.asIdeal →
            ((J l.length).map
              (algebraMap M.CoordinateRing (Localization.AtPrime q.asIdeal))).IsRadical) := by
  exact reduced_cut_flag_of_coordinate_local_conditions K hK
    (exists_mixed_cut_flag_with_coordinate_local_conditions K hK)
