-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.embedded_avoidance_on_open
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T02:46:54.976705+00:00
-- url     : https://prove2.me/submissions/3a0d0f43-f95c-41b1-88f0-ca7aa4e8c80b

import Theorems.Thm_PhilipponMultiplicity_Hilbert_cohenMacaulayAt_associated_isMinimal
import Theorems.Thm_PhilipponMultiplicity_SectionThreeSupport_PrimaryDecomposition_associatedPrimes_eq
import Theorems.Thm_Ideal_exists_mem_forall_not_mem_of_forall_not_le
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

end

-- Reused from Solutions/PhilipponCohenMacaulayAvoidance.lean

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace PhilipponMultiplicity.ComponentSelection
variable {R : Type*} [CommRing R] [IsNoetherianRing R]

theorem regular_quotient_of_avoids_associated (L : Ideal R) (x : R)
    (hx : ∀ q ∈ associatedPrimes R (R ⧸ L), x ∉ q) :
    IsRegular (Ideal.Quotient.mk L x) := by
  apply (Commute.isRegular_iff (fun y => mul_comm _ y)).mpr
  apply isLeftRegular_of_non_zero_divisor
  intro z hz
  by_contra hn
  have hz' : x ∈ {r : R | ∃ z : R ⧸ L, z ≠ 0 ∧ r • z = 0} :=
    ⟨z, hn, by simpa only [Algebra.smul_def, Ideal.Quotient.algebraMap_eq] using hz⟩
  rw [← biUnion_associatedPrimes_eq_zero_divisors R (R ⧸ L)] at hz'
  obtain ⟨q, hq, hxq⟩ := Set.mem_iUnion₂.mp hz'
  exact hx q hq hxq

end PhilipponMultiplicity.ComponentSelection

namespace PhilipponMultiplicity.SectionThreeSupport
open ComponentSelection
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Fact E reduced to the substantive Cohen--Macaulay unmixedness theorem.
The prime-avoidance consequences are proved here, not assumed. -/
theorem embedded_avoidance_on_open_of_unmixed
    (hUnmixed : ∀ (I : Ideal M.CoordinateRing) (m : MaximalSpectrum M.CoordinateRing),
      Hilbert.IsCohenMacaulayAt K M.factorCount M.ambientDimension I m →
      ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ I),
        q ≤ m.asIdeal → q ∈ I.minimalPrimes)
    (I : Ideal M.CoordinateRing) (D : PrimaryDecomposition M I)
    (U : MaximalOpenLocus M) (hU : IsLocallyCohenMacaulayOn M I U) :
    (∀ i : Fin D.count, D.IsEmbedded i →
      ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
    (∀ L : Ideal M.CoordinateRing,
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
        Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          ¬ (D.component i).radical ≤ q) ∧
      ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q)) := by
  classical
  have hno : ∀ i : Fin D.count, D.IsEmbedded i →
      ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U := by
    intro i hi ⟨m, hm, hle⟩
    apply hi
    apply hUnmixed I m (hU m hm) _ _ hle
    rw [D.associatedPrimes_eq]
    exact Set.mem_range_self i
  refine ⟨hno, fun L hL => ?_⟩
  have hnot : ∀ i : Fin D.count, D.IsEmbedded i →
      ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
        ¬ (D.component i).radical ≤ q := by
    intro i hi q hq hle
    obtain ⟨m, hm, hqm⟩ := hL q hq
    exact hno i hi ⟨m, hm, hle.trans hqm⟩
  refine ⟨hnot, ?_⟩
  let S := (associatedPrimes.finite M.CoordinateRing (M.CoordinateRing ⧸ L)).toFinset
  have havoid : ∀ q ∈ S, ¬ D.embeddedIntersection ≤ q := by
    intro q hq hle
    have hq' : q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L) :=
      (by simpa only [S, Set.Finite.mem_toFinset] using hq)
    obtain ⟨i, hi⟩ := (finite_iInf_le_prime _ _ hq'.isPrime).mp hle
    split_ifs at hi with hiemb
    · exact hnot i hiemb q hq' (hq'.isPrime.radical_le_iff.mpr hi)
    · exact hq'.isPrime.ne_top (top_unique hi)
  obtain ⟨x, hx, hav⟩ := Ideal.exists_mem_forall_not_mem_of_forall_not_le
    D.embeddedIntersection S (fun q hq =>
      (show q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L) by
        simpa only [S, Set.Finite.mem_toFinset] using hq).isPrime) havoid
  refine ⟨x, hx, regular_quotient_of_avoids_associated L x ?_⟩
  intro q hq
  exact hav q (by simpa only [S, Set.Finite.mem_toFinset] using hq)

end PhilipponMultiplicity.SectionThreeSupport

end

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (D : PrimaryDecomposition M I)
    (U : MaximalOpenLocus M) (hU : IsLocallyCohenMacaulayOn M I U) :
    (∀ i : Fin D.count, D.IsEmbedded i →
      ¬ Hilbert.MeetsOpen K M.factorCount M.ambientDimension (D.component i).radical U) ∧
    (∀ L : Ideal M.CoordinateRing,
      (∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
        Hilbert.MeetsOpen K M.factorCount M.ambientDimension q U) →
      (∀ i : Fin D.count, D.IsEmbedded i →
        ∀ q ∈ associatedPrimes M.CoordinateRing (M.CoordinateRing ⧸ L),
          ¬ (D.component i).radical ≤ q) ∧
      ∃ Q ∈ D.embeddedIntersection, IsRegular (Ideal.Quotient.mk L Q)) := by
  exact embedded_avoidance_on_open_of_unmixed M (PhilipponMultiplicity.Hilbert.cohenMacaulayAt_associated_isMinimal M) I D U hU
