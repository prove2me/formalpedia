-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.component_partition_cut
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:40:00.241481+00:00
-- url     : https://prove2.me/submissions/6ae714a5-9a3d-48b1-bfc4-c372cb279af1

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert

-- Reused from Solutions/PhilipponComponentPartition.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
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

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Fact B, in the actual associated-prime and minimal-prime definitions. -/
theorem component_partition_primes (J I : Ideal M.CoordinateRing) (hle : J ≤ I) :
    (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
      ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
    (∀ p ∈ J.minimalPrimes,
      p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) := by
  constructor
  · intro q hq
    letI := hq.isPrime
    exact Ideal.exists_minimalPrimes_le (hle.trans (le_associatedPrime hq))
  · intro p hp hn hIp
    exact hn (minimalPrime_isAssociated (minimalPrime_of_between hp hle hIp))

private theorem selected_primary_le_prime_iff (J q : Ideal M.CoordinateRing)
    (hq : q.IsPrime)
    (s : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J → Prop)
    [DecidablePred s] :
    (⨅ p, if s p then Hilbert.primaryComponent K M.factorCount M.ambientDimension J p.1
      else ⊤) ≤ q ↔ ∃ p, s p ∧ p.1.asIdeal ≤ q := by
  classical
  letI := Fintype.ofFinite (Hilbert.MinimalComponent K M.factorCount M.ambientDimension J)
  rw [← Finset.inf_univ_eq_iInf, hq.inf_le']
  simp only [Finset.mem_univ, true_and]
  constructor
  · rintro ⟨p, hp⟩
    split_ifs at hp with hs
    · refine ⟨p, hs, ?_⟩
      rw [← Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2]
      exact hq.radical_le_iff.mpr hp
    · exact (hq.ne_top (top_unique hp)).elim
  · rintro ⟨p, hs, hp⟩
    refine ⟨p, ?_⟩
    rw [if_pos hs]
    exact (Ideal.le_radical.trans (le_of_eq
      (Hilbert.primaryComponent_radical K M.factorCount M.ambientDimension J p.1 p.2))).trans hp

/-- Fact C: the cut separates into the discarded cut and the retained support;
the retained minimal primes remain isolated after the cut. -/
theorem component_partition_cut (J I : Ideal M.CoordinateRing) (hle : J ≤ I)
    (P : M.CoordinateRing) (hP : P ∈ I) :
    (J ⊔ Ideal.span {P}).radical =
      (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
    ∀ q ∈ J.minimalPrimes,
      q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      q ∈ (J ⊔ Ideal.span {P}).minimalPrimes := by
  classical
  constructor
  · rw [← Ideal.radical_inf]
    apply radical_eq_of_prime_containment
    intro q hq
    letI := hq
    simp only [hq.inf_le, sup_le_iff, Ideal.span_singleton_le_iff_mem]
    have hd := selected_primary_le_prime_iff M J q hq
      (fun p => p.1.asIdeal ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    have hr := selected_primary_le_prime_iff M J q hq
      (fun p => p.1.asIdeal ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I))
    unfold discardedPart retainedPart
    constructor
    · rintro ⟨hJq, hPq⟩
      obtain ⟨p, hp, hpq⟩ := Ideal.exists_minimalPrimes_le hJq
      let p' : Hilbert.MinimalComponent K M.factorCount M.ambientDimension J :=
        ⟨⟨p, hp.1.1⟩, hp⟩
      by_cases ha : p ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I)
      · exact Or.inr (hr.mpr ⟨p', ha, hpq⟩)
      · exact Or.inl ⟨hd.mpr ⟨p', ha, hpq⟩, hPq⟩
    · rintro (⟨hD, hPq⟩ | hR)
      · obtain ⟨p, _, hpq⟩ := hd.mp hD
        exact ⟨p.2.1.2.trans hpq, hPq⟩
      · obtain ⟨p, hp, hpq⟩ := hr.mp hR
        exact ⟨p.2.1.2.trans hpq, hpq (le_associatedPrime hp hP)⟩
  · intro q hq ha
    apply minimalPrime_of_between hq le_sup_left
    apply sup_le hq.1.2
    rw [Ideal.span_singleton_le_iff_mem]
    exact le_associatedPrime ha hP

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) (hle : J ≤ I)
    (P : M.CoordinateRing) (hP : P ∈ I) :
    (J ⊔ Ideal.span {P}).radical =
      (discardedPart M J I ⊔ Ideal.span {P}).radical ⊓ (retainedPart M J I).radical ∧
    ∀ q ∈ J.minimalPrimes,
      q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) →
      q ∈ (J ⊔ Ideal.span {P}).minimalPrimes := by
  exact PhilipponMultiplicity.SectionThreeSupport.component_partition_cut M J I hle P hP
