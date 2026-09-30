-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.componentSum_le_of_discarded_zero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T10:03:30.689562+00:00
-- url     : https://prove2.me/submissions/be1117d1-11c7-4a29-a100-e0f971b06250

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_eq_of_radical_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_degreeValue_antitone_of_dimension_eq
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
noncomputable section


namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R]

theorem minimalPrime_of_between {J I q : Ideal R}
    (hq : q ∈ J.minimalPrimes) (hJI : J ≤ I) (hIq : I ≤ q) :
    q ∈ I.minimalPrimes :=
  ⟨⟨hq.1.1, hIq⟩, fun r hr hrq => hq.2 ⟨hr.1, hJI.trans hr.2⟩ hrq⟩

theorem le_associatedPrime {I q : Ideal R}
    (hq : q ∈ associatedPrimes R (R ⧸ I)) : I ≤ q := by
  simpa only [Submodule.annihilator_top, Ideal.annihilator_quotient] using
    hq.annihilator_le

theorem minimalPrime_isAssociated [IsNoetherianRing R] {I q : Ideal R}
    (hq : q ∈ I.minimalPrimes) : q ∈ associatedPrimes R (R ⧸ I) := by
  apply Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes R (R ⧸ I)
  simpa only [Ideal.annihilator_quotient] using hq

theorem radical_eq_of_prime_containment (A B : Ideal R)
    (h : ∀ q : Ideal R, q.IsPrime → (A ≤ q ↔ B ≤ q)) : A.radical = B.radical := by
  rw [Ideal.radical_eq_sInf, Ideal.radical_eq_sInf]
  congr 1
  ext q
  exact ⟨fun hq => ⟨(h q hq.2).mp hq.1, hq.2⟩,
    fun hq => ⟨(h q hq.2).mpr hq.1, hq.2⟩⟩

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.ComponentDegree
variable {ι : Type*} [Fintype ι]

theorem eval_nonneg_of_coeff_nonneg (F : MvPolynomial ι ℚ)
    (hF : ∀ e, 0 ≤ coeff e F) (d : ι → ℕ) : 0 ≤ eval (fun i => (d i : ℚ)) F := by
  classical
  rw [eval_eq]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hF e)
    (Finset.prod_nonneg fun i _ => pow_nonneg (Nat.cast_nonneg _) _)

end PhilipponMultiplicity.ComponentDegree

namespace PhilipponMultiplicity.PrimaryComponentSupport

private theorem sum_le_of_finset_injection {α β : Type*} (s : Finset α) (t : Finset β)
    (f : s → β) (hf : Function.Injective f) (hft : ∀ x, f x ∈ t)
    (a : α → ℚ) (b : β → ℚ) (hval : ∀ x, a x.1 ≤ b (f x))
    (hn : ∀ y ∈ t, 0 ≤ b y) : ∑ x ∈ s, a x ≤ ∑ y ∈ t, b y := by
  classical
  calc
    _ = ∑ x ∈ s.attach, a x.1 := (Finset.sum_attach s a).symm
    _ ≤ ∑ x ∈ s.attach, b (f x) := Finset.sum_le_sum (fun x _ => hval x)
    _ = ∑ y ∈ s.attach.image f, b y := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact hft x)
      (fun y hy _ => hn y hy)

open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

end PhilipponMultiplicity.PrimaryComponentSupport

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem primaryComponent_degreeValue_antitone (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (q : PrimeSpectrum M.CoordinateRing)
    (hqJ : q.asIdeal ∈ J.minimalPrimes) (hqI : q.asIdeal ∈ I.minimalPrimes)
    (D : M.FactorIndex → ℕ) :
    degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension I q) D ≤
      degreeValue K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension J q) D := by
  have hJh := primaryComponent_homogeneous M J hJ q hqJ
  have hIh := primaryComponent_homogeneous M I hI q hqI
  have hle : primaryComponent K M.factorCount M.ambientDimension J q ≤
      primaryComponent K M.factorCount M.ambientDimension I q :=
    Ideal.comap_mono (Ideal.map_mono hJI)
  have hdim := idealDimension_eq_of_radical_eq M _ _ hJh hIh
    ((primaryComponent_radical K M.factorCount M.ambientDimension J q hqJ).trans
      (primaryComponent_radical K M.factorCount M.ambientDimension I q hqI).symm)
  exact degreeValue_antitone_of_dimension_eq M _ _ hJh hIh hle hdim D

end PhilipponMultiplicity.Hilbert

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- At the last stage, every relevant component of the final ideal was
already an isolated component of the intermediate ideal. -/
theorem relevant_minimalPrimes_subset_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (q : Ideal M.CoordinateRing) (hq : q ∈ I.minimalPrimes)
    (hrel : Hilbert.IsRelevant K M.factorCount M.ambientDimension q) :
    q ∈ J.minimalPrimes := by
  letI := hq.1.1
  obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hJI.trans hq.1.2)
  have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
    fun h => hrel (h.trans hpq)
  have heq : p = q := by
    by_cases ha : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)
    · exact le_antisymm hpq (hq.2 ⟨hp.1.1, le_associatedPrime ha⟩ hpq)
    · by_contra hne
      have hs := Hilbert.relevant_prime_dimension_strict M p q hp.1.1 hq.1.1
        (Hilbert.minimalPrime_homogeneous M J p hJ hp)
        (Hilbert.minimalPrime_homogeneous M I q hI hq) hrel (lt_of_le_of_ne hpq hne)
      have := hbound p hp hprel ha
      omega
  exact heq ▸ hp


end PhilipponMultiplicity.SectionThreeSupport

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree PrimaryComponentSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Componentwise degree comparison retains the actual primary multiplicities.
The hypothesis is only on minimal primes that contribute to the chosen locus. -/
theorem componentSum_le_of_relevant_minimalPrimes (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I) (U : MaximalOpenLocus M)
    (hmin : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U → q ∈ J.minimalPrimes)
    (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
  let s := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let t := Finset.univ.filter fun q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J =>
    Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
      Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
  let f : s → Hilbert.MinimalComponent K M.factorCount M.ambientDimension J := fun q =>
    ⟨q.1.1, hmin q.1.1.asIdeal q.1.2
      (Finset.mem_filter.mp q.2).2.1 (Finset.mem_filter.mp q.2).2.2⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J => x.1) h
  have hft (q : s) : f q ∈ t :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp q.2).2⟩
  unfold componentHilbertSum Hilbert.componentSum
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  change (∑ q ∈ s, Hilbert.degreeValue K M.factorCount M.ambientDimension
      (Hilbert.primaryComponent K M.factorCount M.ambientDimension I q.1) D) ≤
    ∑ q ∈ t, Hilbert.degreeValue K M.factorCount M.ambientDimension
      (Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1) D
  exact sum_le_of_finset_injection s t f hf hft _ _
    (fun q => Hilbert.primaryComponent_degreeValue_antitone M J I hJ hI hJI q.1.1 (f q).2 q.1.2 D)
    (fun q _ => degreeValue_nonneg M _ (Hilbert.primaryComponent_homogeneous M J hJ q.1 q.2) D)

/-- The scheme-theoretic endpoint of Proposition 3.3's descending induction.
Unlike the radical endpoint, this bounds the degrees of the actual primary
components, including their multiplicities. -/
theorem componentSum_le_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by
  exact componentSum_le_of_relevant_minimalPrimes M J I hJ hI hJI U
    (fun q hq hrel _ =>
      relevant_minimalPrimes_subset_of_discarded_zero M J I hJ hI hJI hbound q hq hrel) D

end PhilipponMultiplicity.SectionThreeSupport

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I U D ≤ componentHilbertSum M J U D := by
  exact PhilipponMultiplicity.SectionThreeSupport.componentSum_le_of_discarded_zero M J I hJ hI hJI hbound U D
