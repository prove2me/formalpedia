-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.dimensionSlice_mono
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:44:50.300007+00:00
-- url     : https://prove2.me/submissions/b9ee9740-cb9e-47f9-934b-b5b4639ed014

import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_dimension_strict
import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponDimensionSlice.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection

theorem finite_iInf_le_prime {R ι : Type*} [CommRing R] [Finite ι]
    (A : ι → Ideal R) (q : Ideal R) (hq : q.IsPrime) :
    (⨅ i, A i) ≤ q ↔ ∃ i, A i ≤ q := by
  classical
  letI := Fintype.ofFinite ι
  simpa only [Finset.inf_univ_eq_iInf, Finset.mem_univ, true_and] using
    (hq.inf_le' (s := Finset.univ) (f := A))

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem dimensionAtLeast_le_prime_iff (J q : Ideal M.CoordinateRing)
    (hq : q.IsPrime) (b : ℕ) :
    dimensionAtLeast M J b ≤ q ↔
      ∃ p : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J,
        Hilbert.IsRelevant K M.factorCount M.ambientDimension p.1.asIdeal ∧
        b ≤ idealDimension M p.1.asIdeal ∧ p.1.asIdeal ≤ q := by
  classical
  unfold dimensionAtLeast
  rw [finite_iInf_le_prime]
  · constructor
    · rintro ⟨p, hp⟩
      split_ifs at hp with h
      · refine ⟨p, h.1, h.2, ?_⟩
        rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
        exact hq.radical_le_iff.mpr hp
      · exact (hq.ne_top (top_unique hp)).elim
    · rintro ⟨p, hr, hd, hp⟩
      refine ⟨p, ?_⟩
      rw [if_pos ⟨hr, hd⟩]
      exact (Ideal.le_radical.trans (le_of_eq
        (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2))).trans hp
  · exact hq

/-- Fact A: agreement of the higher-dimensional supports makes the
dimension-b isolated primary components monotone. -/
theorem dimensionSlice_mono (J J' : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJ' : IsMultihomogeneousIdeal M J')
    (hle : J ≤ J') (b : ℕ)
    (heq : (dimensionAtLeast M J (b + 1)).radical =
      (dimensionAtLeast M J' (b + 1)).radical) :
    dimensionSlice M J b ≤ dimensionSlice M J' b := by
  classical
  unfold dimensionSlice
  refine le_iInf fun q => ?_
  split_ifs with hq
  · letI : q.1.asIdeal.IsPrime := q.1.isPrime
    obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le (hle.trans q.2.1.2)
    have hprel : Hilbert.IsRelevant K M.factorCount M.ambientDimension p :=
      fun h => hq.1 (h.trans hpq)
    have hphom := Hilbert.minimalPrime_homogeneous M J p hJ hp
    have hqhom := Hilbert.minimalPrime_homogeneous M J' q.1.asIdeal hJ' q.2
    have hdim := Hilbert.idealDimension_antitone M p q.1.asIdeal hphom hqhom hpq
    have hpdim : idealDimension M p = b := by
      by_contra hne
      have hb : b + 1 ≤ idealDimension M p := by omega
      have hhigh : dimensionAtLeast M J (b + 1) ≤ q.1.asIdeal :=
        (dimensionAtLeast_le_prime_iff M J q.1.asIdeal q.1.isPrime _).mpr
          ⟨⟨⟨p, hp.1.1⟩, hp⟩, hprel, hb, hpq⟩
      have hhigh' : dimensionAtLeast M J' (b + 1) ≤ q.1.asIdeal := by
        apply q.1.isPrime.radical_le_iff.mp
        rw [← heq]
        exact q.1.isPrime.radical_le_iff.mpr hhigh
      obtain ⟨s, _, hs, hsq⟩ :=
        (dimensionAtLeast_le_prime_iff M J' q.1.asIdeal q.1.isPrime _).mp hhigh'
      have hsEq : s.1.asIdeal = q.1.asIdeal :=
        le_antisymm hsq (q.2.2 s.2.1 hsq)
      rw [hsEq, hq.2] at hs
      omega
    have hpEq : p = q.1.asIdeal := by
      by_contra hne
      have hs := Hilbert.relevant_prime_dimension_strict M p q.1.asIdeal
        hp.1.1 q.1.isPrime hphom hqhom hq.1 (lt_of_le_of_ne hpq hne)
      rw [hpdim, hq.2] at hs
      omega
    have hqJ : q.1.asIdeal ∈ J.minimalPrimes := hpEq ▸ hp
    apply le_trans (b := Hilbert.primaryComponent K M.factorCount M.ambientDimension J q.1)
    · apply iInf_le_of_le (⟨q.1, hqJ⟩ :
        Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
      exact le_of_eq (if_pos hq)
    · exact Ideal.comap_mono (Ideal.map_mono hle)
  · exact le_top

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J J' : Ideal M.CoordinateRing)
    (hJ : IsMultihomogeneousIdeal M J) (hJ' : IsMultihomogeneousIdeal M J')
    (hle : J ≤ J') (b : ℕ)
    (heq : (dimensionAtLeast M J (b + 1)).radical =
      (dimensionAtLeast M J' (b + 1)).radical) :
    dimensionSlice M J b ≤ dimensionSlice M J' b := by
  exact PhilipponMultiplicity.SectionThreeSupport.dimensionSlice_mono M J J' hJ hJ' hle b heq
