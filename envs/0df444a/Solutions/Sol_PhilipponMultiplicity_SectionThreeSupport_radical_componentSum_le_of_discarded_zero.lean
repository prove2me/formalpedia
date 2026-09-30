-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.radical_componentSum_le_of_discarded_zero
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T09:13:08.031421+00:00
-- url     : https://prove2.me/submissions/422a0613-ceff-4a1b-b03b-8c56a02459b1

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
set_option autoImplicit false
set_option maxHeartbeats 1200000
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

private theorem reduced_primaryComponent (I : Ideal M.CoordinateRing)
    (q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical) :
    Hilbert.primaryComponent K M.factorCount M.ambientDimension I.radical q.1 = q.1.asIdeal := by
  have hq : q.1.asIdeal ∈ I.minimalPrimes := by
    simpa only [Ideal.radical_minimalPrimes] using q.2
  change (I.radical.map (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal))).comap
    (algebraMap M.CoordinateRing (Localization.AtPrime q.1.asIdeal)) = q.1.asIdeal
  rw [IsLocalization.map_radical q.1.asIdeal.primeCompl,
    Ideal.comap_radical]
  exact Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension I q.1 hq

private theorem reduced_componentSum (I : Ideal M.CoordinateRing)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D = (by
      classical
      letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
      exact ∑ q : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I,
        if Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U then
          Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D else 0) := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I)
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical)
  let e : Hilbert.MinimalComponent K M.factorCount M.ambientDimension I.radical ≃
      Hilbert.MinimalComponent K M.factorCount M.ambientDimension I :=
    Equiv.subtypeEquivRight fun q => by rw [Ideal.radical_minimalPrimes]
  unfold componentHilbertSum Hilbert.componentSum
  apply Fintype.sum_equiv e
  intro q
  rw [reduced_primaryComponent M I q]
  rfl

private theorem degreeValue_nonneg (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (D : M.FactorIndex → ℕ) :
    0 ≤ Hilbert.degreeValue K M.factorCount M.ambientDimension I D := by
  unfold Hilbert.degreeValue Hilbert.degreeForm
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
  apply mul_nonneg (Nat.cast_nonneg _)
  exact ComponentDegree.eval_nonneg_of_coeff_nonneg _
    (multigraded_hilbert_polynomial_top_coefficients K M I hI).1 D

private theorem sum_le_of_finset_injection {α β : Type*} (s : Finset α) (t : Finset β)
    (f : s → β) (hf : Function.Injective f) (hft : ∀ x, f x ∈ t)
    (a : α → ℚ) (b : β → ℚ) (hval : ∀ x, a x.1 = b (f x))
    (hn : ∀ y ∈ t, 0 ≤ b y) : ∑ x ∈ s, a x ≤ ∑ y ∈ t, b y := by
  classical
  calc
    _ = ∑ x ∈ s.attach, a x.1 := (Finset.sum_attach s a).symm
    _ = ∑ x ∈ s.attach, b (f x) := Finset.sum_congr rfl (fun x _ => hval x)
    _ = ∑ y ∈ s.attach.image f, b y := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
      (by intro y hy; obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hy; exact hft x)
      (fun y hy _ => hn y hy)

/-- The radical component-sum comparison at the endpoint of the descending
induction. The degree bound for the cuts themselves is not assumed or proved
here: only the final comparison of I with the last intermediate ideal. -/
theorem radical_componentSum_le_of_discarded_zero (J I : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hI : IsMultihomogeneousIdeal M I)
    (hJI : J ≤ I)
    (hbound : ∀ q ∈ J.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      q ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      idealDimension M q ≤ 0)
    (U : MaximalOpenLocus M) (D : M.FactorIndex → ℕ) :
    componentHilbertSum M I.radical U D ≤ componentHilbertSum M J.radical U D := by
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
    ⟨q.1.1, relevant_minimalPrimes_subset_of_discarded_zero M J I hJ hI hJI hbound q.1.1.asIdeal
      q.1.2 (Finset.mem_filter.mp q.2).2.1⟩
  have hf : Function.Injective f := by
    intro q r h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J => x.1) h
  have hft (q : s) : f q ∈ t :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp q.2).2⟩
  rw [reduced_componentSum M I U D, reduced_componentSum M J U D]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  change (∑ q ∈ s, Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D) ≤
    ∑ q ∈ t, Hilbert.degreeValue K M.factorCount M.ambientDimension q.1.asIdeal D
  exact sum_le_of_finset_injection s t f hf hft _ _ (fun _ => rfl) (fun q _ =>
    degreeValue_nonneg M q.1.asIdeal (Hilbert.minimalPrime_homogeneous M J q.1.asIdeal hJ q.2) D)


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
    componentHilbertSum M I.radical U D ≤ componentHilbertSum M J.radical U D := by
  exact PhilipponMultiplicity.SectionThreeSupport.radical_componentSum_le_of_discarded_zero M J I hJ hI hJI hbound U D
