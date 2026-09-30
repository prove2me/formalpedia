-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.component_partition_primes
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:40:00.051829+00:00
-- url     : https://prove2.me/submissions/5f8129b9-697c-4a69-8098-30beb4b51d68

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

end PhilipponMultiplicity.SectionThreeSupport
end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K) (J I : Ideal M.CoordinateRing) (hle : J ≤ I) :
    (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
      ∃ p ∈ J.minimalPrimes, p ≤ q) ∧
    (∀ p ∈ J.minimalPrimes,
      p ∉ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I) → ¬ I ≤ p) := by
  exact PhilipponMultiplicity.SectionThreeSupport.component_partition_primes M J I hle
