-- Prove2me | solution 1 for PhilipponMultiplicity.exists_principal_open_smooth_mixed_zero_locus
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-05T12:37:17.578772+00:00
-- url     : https://prove2.me/submissions/1f5cb344-a275-4851-bbce-e357cd0837d1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_PhilipponMultiplicity_exists_principal_open_pointwise_smooth_mixed_zero_locus
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Definitions.Def_PhilipponMultiplicity_Geometry
import Definitions.Def_PhilipponMultiplicity_MixedFlagParameters
import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Smooth.Locus
import Mathlib.RingTheory.Spectrum.Prime.Jacobson

set_option autoImplicit false

section

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

theorem primeCompl_map_quotient {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    p.primeCompl.map (Ideal.Quotient.mk I) = (p.map (Ideal.Quotient.mk I)).primeCompl := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  ext x
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨s, hs, heq⟩
    change Ideal.Quotient.mk I r ∉ p.map (Ideal.Quotient.mk I)
    rw [← heq, Ideal.mem_quotient_iff_mem hIp]
    exact hs
  · intro h
    refine ⟨r, ?_, rfl⟩
    exact fun hr => h (Ideal.mem_map_of_mem _ hr)

/-- The two actual rings obtained by quotienting and localizing commute.
This is the identification needed between smooth affine rings and the local
quotients in Philippon's definition. -/
def localizedQuotientEquiv {R : Type*} [CommRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ≃ₐ[R ⧸ I]
      Localization.AtPrime (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  let B := (Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))
  haveI : IsLocalization (p.map (Ideal.Quotient.mk I)).primeCompl B := by
    rw [← primeCompl_map_quotient I p hIp]
    exact inferInstanceAs (IsLocalization (Algebra.algebraMapSubmonoid (R ⧸ I) p.primeCompl) B)
  exact IsLocalization.algEquiv (p.map (Ideal.Quotient.mk I)).primeCompl B _

end PhilipponMultiplicity.AlgebraicGroupCM

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.ClosedPointSmoothness

/-- On an open subset of a finite type affine scheme over a field, smoothness
can be tested on points closed in the ambient affine scheme. -/
theorem smooth_on_open_of_maximal
    (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R]
    (U : Set (PrimeSpectrum R)) (hU : IsOpen U)
    (h : ∀ q ∈ U, q.asIdeal.IsMaximal → Algebra.IsSmoothAt K q.asIdeal) :
    ∀ q ∈ U, Algebra.IsSmoothAt K q.asIdeal := by
  letI : IsJacobsonRing R := isJacobsonRing_of_finiteType (A := K) (B := R)
  letI : Algebra.FinitePresentation K R :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  intro q hq
  by_contra hn
  obtain ⟨m, ⟨hmU, hmns⟩, hmclosed⟩ := nonempty_inter_closedPoints
    (Z := U \ Algebra.smoothLocus K R) ⟨q, hq, hn⟩
    (hU.isLocallyClosed.inter Algebra.isOpen_smoothLocus.isClosed_compl.isLocallyClosed)
  exact hmns (h m hmU ((PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hmclosed))

/-- Smoothness is unchanged by commuting quotient and localization. The
equivalence respects the ground field, not just the underlying rings. -/
theorem point_local_iff_quotient_local
    {K R : Type*} [CommRing K] [CommRing R] [Algebra K R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) :
    letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
      Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
    Algebra.FormallySmooth K
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) ↔
      Algebra.IsSmoothAt K (p.map (Ideal.Quotient.mk I)) := by
  letI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : IsScalarTower K (R ⧸ I)
      ((Localization.AtPrime p) ⧸ I.map (algebraMap R (Localization.AtPrime p))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact Algebra.FormallySmooth.iff_of_equiv
    ((AlgebraicGroupCM.localizedQuotientEquiv I p hIp).restrictScalars K)

variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- The punctured multicone is open: in each finite coordinate block at least
one coordinate must remain outside the prime. -/
theorem isOpen_punctured_quotient (I : Ideal M.CoordinateRing) :
    IsOpen {q : PrimeSpectrum (M.CoordinateRing ⧸ I) |
      ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal} := by
  simp only [Set.ofPred_forall, Set.ofPred_exists]
  exact isOpen_iInter_of_finite (fun i => isOpen_iUnion (fun j =>
    (PrimeSpectrum.basicOpen (Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩))).isOpen))

/-- Hilbert's Nullstellensatz identifies every closed point of the quotient
with an actual coordinate tuple satisfying its equations and block conditions. -/
theorem maximal_is_point [IsAlgClosed K]
    (I : Ideal M.CoordinateRing) (q : PrimeSpectrum (M.CoordinateRing ⧸ I))
    (hq : q.asIdeal.IsMaximal)
    (hblocks : ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) :
    ∃ v : M.Variable → K,
      (∀ i : M.FactorIndex,
        (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) ∧
      (∀ P ∈ I, MvPolynomial.eval v P = 0) ∧
      q.asIdeal = (MvPolynomial.vanishingIdeal K {v}).map (Ideal.Quotient.mk I) := by
  letI : q.asIdeal.IsMaximal := hq
  let p := q.asIdeal.comap (Ideal.Quotient.mk I)
  have hp : p.IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨v, hv⟩ := MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal K hp
  have hIp : I ≤ p := by
    intro P hP
    change Ideal.Quotient.mk I P ∈ q.asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hP]
    exact q.asIdeal.zero_mem
  refine ⟨v, ?_, ?_, ?_⟩
  · intro i
    obtain ⟨j, hj⟩ := hblocks i
    intro hz
    apply hj
    change MvPolynomial.X ⟨i,j⟩ ∈ p
    rw [hv]
    have hvj := congrFun hz j
    simpa [MvPolynomial.vanishingIdeal] using hvj
  · intro P hP
    have hm := hIp hP
    rw [hv] at hm
    simpa [MvPolynomial.vanishingIdeal] using hm
  · rw [← hv]
    exact (Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q.asIdeal).symm

/-- Smoothness at actual nonzero-block tuples controls every prime of the
punctured multicone, including its nonclosed points. -/
theorem smooth_punctured_of_pointwise [IsAlgClosed K]
    (I : Ideal M.CoordinateRing)
    (h : ∀ v : M.Variable → K,
      (∀ i : M.FactorIndex,
        (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
      (∀ P ∈ I, MvPolynomial.eval v P = 0) →
      Algebra.FormallySmooth K
        ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
          I.map (algebraMap M.CoordinateRing
            (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v}))))) :
    ∀ q : PrimeSpectrum (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
      Algebra.IsSmoothAt K q.asIdeal := by
  apply smooth_on_open_of_maximal K (M.CoordinateRing ⧸ I) _
    (isOpen_punctured_quotient M I)
  intro q hq hmax
  obtain ⟨v, hv, hIv, hqv⟩ := maximal_is_point M I q hmax hq
  have hIp : I ≤ MvPolynomial.vanishingIdeal K {v} := by
    intro P hP
    simpa [MvPolynomial.vanishingIdeal] using hIv P hP
  have hs := (point_local_iff_quotient_local (K := K) I
    (MvPolynomial.vanishingIdeal K {v}) hIp).mp (h v hv hIv)
  simpa only [← hqv] using hs

end PhilipponMultiplicity.ClosedPointSmoothness

end

end


section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace PhilipponMultiplicity.PolynomialJacobian

/-- Reuse the base-field transfers from PhilipponGroupPrimeComponents,
PhilipponPrimeImageReduction and PhilipponCodimensionContainmentReduction. -/
theorem basefield_facts {K : Type*} [NontriviallyNormedField K]
    (hK : IsPhilipponBaseField K) : CompleteSpace K ∧ IsAlgClosed K ∧ CharZero K := by
  have hcomplete : CompleteSpace K := by
    rcases hK with ⟨e, he⟩ | ⟨p, hp, h⟩
    · exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, he⟩ := h
      exact (he.isUniformInducing.completeSpace_congr e.surjective).mpr inferInstance
  have hchar : CharZero K := by
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact e.toRingHom.charZero
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact e.toRingHom.charZero
  have hclosed : IsAlgClosed K := by
    have transfer (F : Type) [Field F] [IsAlgClosed F] (e : K ≃+* F) : IsAlgClosed K := by
      apply IsAlgClosed.of_exists_root K
      intro P _ hP
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_eval₂_eq_zero e.toRingHom P
        (ne_of_gt (Polynomial.degree_pos_of_irreducible hP))
      refine ⟨e.symm x, ?_⟩
      apply e.injective
      rw [map_zero]
      change e.toRingHom (P.eval (e.symm x)) = 0
      rw [← Polynomial.eval₂_at_apply]
      change P.eval₂ e.toRingHom (e (e.symm x)) = 0
      simpa only [RingEquiv.apply_symm_apply] using hx
    rcases hK with ⟨e, _⟩ | ⟨p, hp, h⟩
    · exact transfer ℂ e
    · letI : Fact p.Prime := ⟨hp⟩
      obtain ⟨e, _⟩ := h
      exact transfer (PadicComplex p) e
  exact ⟨hcomplete, hclosed, hchar⟩

end PolynomialJacobian
end PhilipponMultiplicity
end

end


section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators Topology
noncomputable section

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem smooth_mixed_zero_locus_of_pointwise
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K)
    (hgeometry : ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ v : M.Variable → K,
                (∀ i : M.FactorIndex,
                  (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
                (∀ P ∈ MixedFlag.ideal M (M.vanishingIdeal W) l c l.length,
                  MvPolynomial.eval v P = 0) →
                Algebra.FormallySmooth K
                  ((Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})) ⧸
                    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length).map
                      (algebraMap M.CoordinateRing
                        (Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})))))) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by
  letI : IsAlgClosed K := (PolynomialJacobian.basefield_facts hK).2.1
  intro M W hW hirr α hα hdim B hB hBW hne l hl
  obtain ⟨F, hF, hgood⟩ := hgeometry M W hW hirr α hα hdim B hB hBW hne l hl
  refine ⟨F, hF, ?_⟩
  intro c hc
  obtain ⟨hfinite, hdisjoint, hsmooth⟩ := hgood c hc
  exact ⟨hfinite, hdisjoint, ClosedPointSmoothness.smooth_punctured_of_pointwise M
    (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length) hsmooth⟩

end PhilipponMultiplicity

end

end

set_option maxHeartbeats 1000000
open PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport
open scoped BigOperators Topology

theorem solution
    (K : Type*) [NontriviallyNormedField K] (hK : IsPhilipponBaseField K) :
    ∀ (M : MultiProjectiveSpace K) (W : Set M.Point),
      @IsClosed _ M.zariskiTopology W → @IsIrreducible _ M.zariskiTopology W →
      ∀ (α : M.FactorIndex → ℕ), (∀ i, α i ≤ M.ambientDimension i) →
      (∑ i, α i = locusDimension M W) →
      ∀ B : Set M.Point, @IsClosed _ M.zariskiTopology B → B ⊆ W →
      (W \ B).Nonempty →
      ∀ l : List M.FactorIndex, (∀ i, l.count i = α i) →
        ∃ F : MvPolynomial (Fin l.length × M.Variable) K, F ≠ 0 ∧
          ∀ c : Fin l.length → M.Variable → K,
            MvPolynomial.eval (Function.uncurry c) F ≠ 0 →
            ({x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0}).Finite ∧
            Disjoint {x : M.Point | x ∈ W ∧
              ∀ j : Fin l.length, M.eval (MixedFlag.polynomial M l c j) x = 0} B ∧
            (∀ q : PrimeSpectrum (M.CoordinateRing ⧸
                  MixedFlag.ideal M (M.vanishingIdeal W) l c l.length),
                (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                  Ideal.Quotient.mk (MixedFlag.ideal M (M.vanishingIdeal W) l c l.length)
                    (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
                Algebra.IsSmoothAt K q.asIdeal) := by
  exact smooth_mixed_zero_locus_of_pointwise K hK
    (exists_principal_open_pointwise_smooth_mixed_zero_locus K hK)
