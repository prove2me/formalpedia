-- Prove2me | solution 1 for PhilipponMultiplicity.exists_mixed_cut_flag_with_regular_local_final_quotients
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-04T18:08:15.238913+00:00
-- url     : https://prove2.me/submissions/1252746a-f450-457c-95d2-c0345c9a507c

import Theorems.Thm_PhilipponMultiplicity_exists_associated_prime_avoiding_smooth_mixed_cut_flag
import Definitions.Def_P2M_Util
import Definitions.Def_PhilipponMultiplicity_GeometricSupport
import Mathlib
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Localization.AtPrime.Basic
import Mathlib.RingTheory.Localization.Ideal
import Mathlib.RingTheory.Localization.LocalizationLocalization
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.StandardSmooth

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

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 800000

noncomputable section

open IsLocalRing Localization

namespace ChildB

private theorem isNoetherianRing_of_essFiniteType (R S : Type*) [CommRing R] [CommRing S]
    [Algebra R S] [IsNoetherianRing R] [Algebra.EssFiniteType R S] :
    IsNoetherianRing S := by
  haveI hN : IsNoetherianRing (Algebra.EssFiniteType.subalgebra R S) :=
    Algebra.FiniteType.isNoetherianRing R _
  exact IsLocalization.isNoetherianRing (Algebra.EssFiniteType.submonoid R S) S hN

end ChildB

theorem etaleRegularAt
    (A B : Type*) [CommRing A] [CommRing B] [Algebra A B] [Algebra.Etale A B]
    (q : Ideal B) [q.IsPrime]
    (hreg : IsRegularLocalRing (Localization.AtPrime (q.comap (algebraMap A B)))) :
    IsRegularLocalRing (Localization.AtPrime q) := by
  haveI := hreg
  haveI hlo : q.LiesOver (q.comap (algebraMap A B)) := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver (q.comap (algebraMap A B)) q

  haveI : Algebra.FormallyUnramified A B := inferInstance
  haveI hIU : Algebra.IsUnramifiedAt A q := by
    unfold Algebra.IsUnramifiedAt
    infer_instance
  haveI hEFTa : Algebra.EssFiniteType A (Localization.AtPrime q) := inferInstance
  haveI hEFT : Algebra.EssFiniteType (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := Algebra.EssFiniteType.of_comp A _ _
  haveI hNoeth : IsNoetherianRing (Localization.AtPrime q) :=
    ChildB.isNoetherianRing_of_essFiniteType (Localization.AtPrime (q.comap (algebraMap A B))) _

  have hmap : (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).map
      (algebraMap _ (Localization.AtPrime q)) = maximalIdeal (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.map_maximalIdeal

  have h1 : (maximalIdeal (Localization.AtPrime q)).spanFinrank ≤
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))).spanFinrank := by
    rw [← hmap]
    exact Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)

  haveI : Module.Flat A B := inferInstance
  haveI hflat : Module.Flat (Localization.AtPrime (q.comap (algebraMap A B)))
      (Localization.AtPrime q) := inferInstance

  haveI hlom2 : (maximalIdeal (Localization.AtPrime q)).LiesOver
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B)))) := by
    constructor
    ext x
    rw [Ideal.under_def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal,
        IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, mem_nonunits_iff]
    exact not_iff_not.mpr
      ⟨fun h => IsLocalHom.map_nonunit x h, fun h => h.map (algebraMap _ _)⟩ |>.symm

  have h2 := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown
    (R := Localization.AtPrime (q.comap (algebraMap A B))) (S := Localization.AtPrime q)
    (maximalIdeal (Localization.AtPrime (q.comap (algebraMap A B))))
    (maximalIdeal (Localization.AtPrime q))

  refine IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ ?_
  calc ((maximalIdeal (Localization.AtPrime q)).spanFinrank : WithBot ℕ∞)
      ≤ ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h1
    _ = ringKrullDim (Localization.AtPrime (q.comap (algebraMap A B))) :=
        hreg.spanFinrank_maximalIdeal
    _ = ((maximalIdeal (Localization.AtPrime
          (q.comap (algebraMap A B)))).height : WithBot ℕ∞) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim.symm
    _ ≤ ((maximalIdeal (Localization.AtPrime q)).height : WithBot ℕ∞) := by
        rw [h2]
        exact_mod_cast le_self_add
    _ = ringKrullDim (Localization.AtPrime q) :=
        IsLocalRing.maximalIdeal_height_eq_ringKrullDim

end

end S_isRegularLocalRing_localization_atPrime_of_etale_of_comap
end P2MW
export P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap (etaleRegularAt)


end


section

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.AlgebraicGroupCM

/-- Standard smooth presentations are étale over a polynomial algebra, whose
prime localizations are regular. -/
theorem regularAt_of_standardSmooth (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.IsStandardSmooth K R] (q : Ideal R) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  obtain ⟨n, f, hf, he⟩ := RingHom.IsStandardSmooth.exists_etale_mvPolynomial
    (f := algebraMap K R) (RingHom.isStandardSmooth_algebraMap.mpr inferInstance)
  algebraize [f]
  haveI : IsRegularRing K := inferInstance
  haveI : IsRegularRing (MvPolynomial (Fin n) K) :=
    MvPolynomial.isRegularRing_of_isRegularRing K
  exact P2MW.S_isRegularLocalRing_localization_atPrime_of_etale_of_comap.etaleRegularAt
    (MvPolynomial (Fin n) K) R q
    (IsRegularRing.isRegularLocalRing_localization _)

/-- Smoothness at a prime suffices: choose a standard smooth neighbourhood
and identify its localization with the original local ring. -/
theorem regularAt_of_smoothAt (K R : Type*) [Field K] [CommRing R] [Algebra K R]
    [Algebra.FinitePresentation K R] (p : Ideal R) [hp : p.IsPrime]
    [Algebra.IsSmoothAt K p] : IsRegularLocalRing (Localization.AtPrime p) := by
  obtain ⟨f, hf, hstd⟩ := Algebra.IsSmoothAt.exists_notMem_isStandardSmooth K p
  letI := hstd
  have hdis : Disjoint (Submonoid.powers f : Set R) (p : Set R) :=
    (Ideal.disjoint_powers_iff_notMem_of_isPrime f).mpr hf
  let q := p.map (algebraMap R (Localization.Away f))
  haveI : q.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint
    (Submonoid.powers f) (Localization.Away f) p hp hdis
  have heq : q.comap (algebraMap R (Localization.Away f)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint (Submonoid.powers f)
      (Localization.Away f) hp hdis
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    regularAt_of_standardSmooth K (Localization.Away f) q
  haveI : IsLocalization p.primeCompl (Localization.AtPrime q) := by
    have heq' : (q.comap (algebraMap R (Localization.Away f))).primeCompl = p.primeCompl := by
      ext x
      change x ∉ q.comap (algebraMap R (Localization.Away f)) ↔ x ∉ p
      rw [heq]
    rw [← heq']
    infer_instance
  exact IsRegularLocalRing.of_ringEquiv
    ((IsLocalization.algEquiv p.primeCompl (Localization.AtPrime p)
      (Localization.AtPrime q)).symm.toRingEquiv)

end PhilipponMultiplicity.AlgebraicGroupCM

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.PrimeAvoidance

/-- Only associated primes contained in the localization prime can obstruct
regularity after localization. -/
theorem regular_atPrime_of_avoids_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) [p.IsPrime] (a : R)
    (h : ∀ q ∈ associatedPrimes R R, q ≤ p → a ∉ q) :
    IsSMulRegular (Localization.AtPrime p)
      (algebraMap R (Localization.AtPrime p) a) := by
  let S := Localization.AtPrime p
  by_contra hn
  have hm : algebraMap R S a ∈ ⋃ q ∈ associatedPrimes S S, (q : Set S) := by
    rw [biUnion_associatedPrimes_eq_compl_regular]
    exact hn
  obtain ⟨q, hq, ha⟩ := Set.mem_iUnion₂.mp hm
  have hqa : q.comap (algebraMap R S) ∈ associatedPrimes R R :=
    Module.associatedPrimes.comap_mem_associatedPrimes_of_mem_associatedPrimes_of_isLocalizedModule_of_fg
      p.primeCompl (Algebra.linearMap R S) q hq (IsNoetherian.noetherian _)
  have hle : q.comap (algebraMap R S) ≤ p := by
    have hd := (IsLocalization.disjoint_under_iff p.primeCompl S q).mpr hq.1.ne_top
    simpa only [Ideal.primeCompl, Submonoid.coe_set_mk, Subsemigroup.coe_set_mk,
      Set.disjoint_compl_left_iff_subset] using! hd
  exact h _ hqa hle ha

/-- Quotienting and localizing transfer associated-prime avoidance to the
precise ideal-membership injectivity condition used in a mixed cut flag. -/
theorem mul_mem_localized_of_avoids_associatedPrimes
    {R : Type*} [CommRing R] [IsNoetherianRing R]
    (I p : Ideal R) [p.IsPrime] (hIp : I ≤ p) (a : R)
    (h : ∀ q ∈ associatedPrimes (R ⧸ I) (R ⧸ I),
      q ≤ p.map (Ideal.Quotient.mk I) → Ideal.Quotient.mk I a ∉ q) :
    ∀ x : Localization.AtPrime p,
      algebraMap R (Localization.AtPrime p) a * x ∈
        I.map (algebraMap R (Localization.AtPrime p)) →
      x ∈ I.map (algebraMap R (Localization.AtPrime p)) := by
  let Q := R ⧸ I
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa using hIp)
  let S := Localization.AtPrime p
  let J := I.map (algebraMap R S)
  let e := AlgebraicGroupCM.localizedQuotientEquiv I p hIp
  have hr := regular_atPrime_of_avoids_associatedPrimes q (Ideal.Quotient.mk I a) h
  have hecoeff := e.commutes (Ideal.Quotient.mk I a)
  change e (Ideal.Quotient.mk J (algebraMap R S a)) =
    algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) at hecoeff
  intro x hx
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change Ideal.Quotient.mk J x = 0
  apply e.injective
  apply hr
  change algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) *
      e (Ideal.Quotient.mk J x) =
    algebraMap Q (Localization.AtPrime q) (Ideal.Quotient.mk I a) * e 0
  rw [map_zero, mul_zero, ← hecoeff, ← map_mul, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]

end PrimeAvoidance

namespace MultiProjectiveSpace
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- A prime below the evaluation prime of a nonzero-block point still
contains no entire coordinate block. -/
theorem nonzero_blocks_below_evaluation
    (I : Ideal M.CoordinateRing) (v : M.Variable → K)
    (hI : ∀ P ∈ I, MvPolynomial.eval v P = 0)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (q : Ideal (M.CoordinateRing ⧸ I))
    (hq : q ≤ (MvPolynomial.vanishingIdeal K {v}).map (Ideal.Quotient.mk I)) :
    ∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
      Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q := by
  have hIp : I ≤ MvPolynomial.vanishingIdeal K {v} := by
    intro P hP
    simpa [MvPolynomial.vanishingIdeal] using hI P hP
  intro i
  obtain ⟨j, hj⟩ := Function.ne_iff.mp (hv i)
  refine ⟨j, fun hc => hj ?_⟩
  have hm := (Ideal.mem_quotient_iff_mem hIp).mp (hq hc)
  simpa [MvPolynomial.vanishingIdeal] using hm

/-- Avoiding the associated primes on the punctured multicone makes a cut
injective in every geometric point-local quotient. -/
theorem point_local_injective_of_associated_prime_avoidance
    (I : Ideal M.CoordinateRing) (P : M.CoordinateRing)
    (h : ∀ q ∈ associatedPrimes (M.CoordinateRing ⧸ I) (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q) →
      Ideal.Quotient.mk I P ∉ q)
    (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (hI : ∀ Q ∈ I, MvPolynomial.eval v Q = 0) :
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    let f := algebraMap M.CoordinateRing R
    ∀ Q : R, f P * Q ∈ I.map f → Q ∈ I.map f := by
  apply PrimeAvoidance.mul_mem_localized_of_avoids_associatedPrimes
  · intro Q hQ
    simpa [MvPolynomial.vanishingIdeal] using hI Q hQ
  · intro q hq hle
    exact h q hq (M.nonzero_blocks_below_evaluation I v hI hv q hle)

/-- Smoothness on the punctured affine multicone gives regularity of the
ordinary point-local quotient, with all scaling directions retained. -/
theorem point_local_regular_of_smooth_punctured_cone
    (I : Ideal M.CoordinateRing)
    (h : ∀ q : PrimeSpectrum (M.CoordinateRing ⧸ I),
      (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
        Ideal.Quotient.mk I (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
      Algebra.IsSmoothAt K q.asIdeal)
    (v : M.Variable → K)
    (hv : ∀ i : M.FactorIndex,
      (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0)
    (hI : ∀ P ∈ I, MvPolynomial.eval v P = 0) :
    let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
    IsRegularLocalRing (R ⧸ I.map (algebraMap M.CoordinateRing R)) := by
  let p := MvPolynomial.vanishingIdeal K {v}
  have hIp : I ≤ p := by
    intro P hP
    simpa [p, MvPolynomial.vanishingIdeal] using hI P hP
  let q := p.map (Ideal.Quotient.mk I)
  letI : q.IsPrime := Ideal.map_isPrime_of_surjective
    Ideal.Quotient.mk_surjective (by simpa using hIp)
  letI : Algebra.IsSmoothAt K q := h ⟨q, inferInstance⟩
    (M.nonzero_blocks_below_evaluation I v hI hv q le_rfl)
  letI : Algebra.FinitePresentation K (M.CoordinateRing ⧸ I) :=
    Algebra.FinitePresentation.of_finiteType.mp inferInstance
  letI : IsRegularLocalRing (Localization.AtPrime q) :=
    AlgebraicGroupCM.regularAt_of_smoothAt K (M.CoordinateRing ⧸ I) q
  exact IsRegularLocalRing.of_ringEquiv
    (R := Localization.AtPrime q)
    (AlgebraicGroupCM.localizedQuotientEquiv I p hIp).symm.toRingEquiv

end MultiProjectiveSpace
end PhilipponMultiplicity

end

end


section

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators Topology

namespace PhilipponMultiplicity
open SectionThree SectionThreeSupport

theorem regular_cut_flag_of_associated_prime_avoidance_and_smoothness
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
            ∀ q ∈ associatedPrimes
                (M.CoordinateRing ⧸ J k) (M.CoordinateRing ⧸ J k),
              (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
                Ideal.Quotient.mk (J k) (MvPolynomial.X ⟨i,j⟩) ∉ q) →
              Ideal.Quotient.mk (J k) (P k) ∉ q) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ q : PrimeSpectrum (M.CoordinateRing ⧸ J l.length),
            (∀ i : M.FactorIndex, ∃ j : Fin (M.ambientDimension i + 1),
              Ideal.Quotient.mk (J l.length) (MvPolynomial.X ⟨i,j⟩) ∉ q.asIdeal) →
            Algebra.IsSmoothAt K q.asIdeal)) :
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
              let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
              let f := algebraMap M.CoordinateRing R
              ∀ Q : R, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
            IsRegularLocalRing (R ⧸ (J l.length).map (algebraMap M.CoordinateRing R))) := by
  intro M W hW hirr α hα hdim B hB hBW hnonempty
  obtain ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, hstep, hgeometry,
    hfinal⟩ := hchoice M W hW hirr α hα hdim B hB hBW hnonempty
  refine ⟨L, hL, hfinite, hdisjoint, l, P, J, hcount, hfirst, ?_, hgeometry, ?_⟩
  · intro k hk
    refine ⟨(hstep k hk).1, (hstep k hk).2.1, ?_⟩
    exact M.point_local_injective_of_associated_prime_avoidance
      (J k) (P k) (hstep k hk).2.2
  · exact M.point_local_regular_of_smooth_punctured_cone (J l.length) hfinal

end PhilipponMultiplicity


end

set_option maxHeartbeats 1000000
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
              let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
              let f := algebraMap M.CoordinateRing R
              ∀ Q : R, f (P k) * Q ∈ (J k).map f → Q ∈ (J k).map f) ∧
          (∀ x : M.Point, x ∈ linearSlice M W L ↔
            x ∈ W ∧ ∀ k < l.length, M.eval (P k) x = 0) ∧
          (∀ v : M.Variable → K,
            (∀ i : M.FactorIndex,
              (fun j : Fin (M.ambientDimension i + 1) => v ⟨i,j⟩) ≠ 0) →
            (∀ Q ∈ J l.length, MvPolynomial.eval v Q = 0) →
            let R := Localization.AtPrime (MvPolynomial.vanishingIdeal K {v})
            IsRegularLocalRing (R ⧸ (J l.length).map (algebraMap M.CoordinateRing R))) := by
  exact regular_cut_flag_of_associated_prime_avoidance_and_smoothness K hK
    (exists_associated_prime_avoiding_smooth_mixed_cut_flag K hK)
