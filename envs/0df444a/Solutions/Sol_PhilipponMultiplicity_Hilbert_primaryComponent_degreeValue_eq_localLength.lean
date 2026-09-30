-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.primaryComponent_degreeValue_eq_localLength
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T23:14:32.686989+00:00
-- url     : https://prove2.me/submissions/efd2195a-3490-427e-a90c-f34c12070d66

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_eq_of_radical_eq
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

theorem localLength_primaryComponent (I : Ideal M.CoordinateRing)
    (q : PrimeSpectrum M.CoordinateRing) :
    localLength K M.factorCount M.ambientDimension
        (primaryComponent K M.factorCount M.ambientDimension I q) q =
      localLength K M.factorCount M.ambientDimension I q := by
  unfold localLength primaryComponent
  rw [IsLocalization.map_under q.asIdeal.primeCompl]

/-- A canonical primary component has its support's degree multiplied by
the original quotient's actual generic local length. -/
theorem primaryComponent_degreeValue_eq_localLength (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (primaryComponent K M.factorCount M.ambientDimension I q) d =
      ((localLength K M.factorCount M.ambientDimension I q).toNat : ℚ) *
        idealDegreeValue M q.asIdeal d := by
  classical
  let Q := primaryComponent K M.factorCount M.ambientDimension I q
  have hQ := primaryComponent_homogeneous M I hI q hq
  have hp := primaryComponent_isPrimary K M.factorCount M.ambientDimension I q hq
  have hr := primaryComponent_radical K M.factorCount M.ambientDimension I q hq
  have hmin : Q.minimalPrimes = {q.asIdeal} := by
    rw [Ideal.minimalPrimes_eq_subsingleton hp, hr]
  have hdim : idealDimension M q.asIdeal = idealDimension M Q :=
    (idealDimension_eq_of_radical_eq M Q q.asIdeal hQ
      (minimalPrime_homogeneous M I q.asIdeal hI hq)
      (hr.trans q.isPrime.radical.symm)).symm
  let T := MinimalComponent K M.factorCount M.ambientDimension Q
  let q₀ : T := ⟨q, by rw [hmin]; exact Set.mem_singleton _⟩
  have heq (r : T) : r = q₀ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    simpa only [hmin, Set.mem_singleton_iff] using r.2
  have hformula := component_length_formula M Q hQ d
  unfold topComponentLengthSum at hformula
  rw [Finset.sum_eq_single q₀] at hformula
  · rw [if_pos ⟨hrel, hdim⟩] at hformula
    exact hformula.trans (congrArg (fun n : ℕ∞ => (n.toNat : ℚ) * idealDegreeValue M q.asIdeal d)
      (localLength_primaryComponent M I q))
  · intro r _ hne
    exact (hne (heq r)).elim
  · simp

end PhilipponMultiplicity.Hilbert

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I) (q : PrimeSpectrum M.CoordinateRing)
    (hq : q.asIdeal ∈ I.minimalPrimes)
    (hrel : IsRelevant K M.factorCount M.ambientDimension q.asIdeal)
    (d : M.FactorIndex → ℕ) :
    idealDegreeValue M (primaryComponent K M.factorCount M.ambientDimension I q) d =
      ((localLength K M.factorCount M.ambientDimension I q).toNat : ℚ) *
        idealDegreeValue M q.asIdeal d := by
  exact PhilipponMultiplicity.Hilbert.primaryComponent_degreeValue_eq_localLength M I hI q hq hrel d
