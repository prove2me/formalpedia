-- Prove2me | solution 1 for PhilipponMultiplicity.SectionThreeSupport.componentSum_le_degreeValue_of_equidimensional
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-26T23:16:16.576985+00:00
-- url     : https://prove2.me/submissions/e89ba2cd-75ee-4821-8a4a-173106ce5847

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_component_length_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_primaryComponent_degreeValue_eq_localLength
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_multigraded_hilbert_polynomial_top_coefficients
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
noncomputable section

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

namespace PhilipponMultiplicity.SectionThreeSupport
open SectionThree
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- On an equidimensional relevant support, selecting an open locus cannot
increase the total Hilbert degree. All canonical primary multiplicities remain. -/
theorem componentSum_le_degreeValue_of_equidimensional (I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I U d ≤ idealDegreeValue M I d := by
  classical
  rw [Hilbert.component_length_formula M I hI d]
  unfold componentHilbertSum Hilbert.componentSum topComponentLengthSum
  apply Finset.sum_le_sum
  intro q _
  by_cases hr : Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal
  · by_cases hu : Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U
    · rw [if_pos ⟨hr, hu⟩, if_pos ⟨hr, hdim q.1.asIdeal q.2 hr⟩]
      exact le_of_eq (Hilbert.primaryComponent_degreeValue_eq_localLength M I hI q.1 q.2 hr d)
    · have hn : ¬ (Hilbert.IsRelevant K M.factorCount M.ambientDimension q.1.asIdeal ∧
          Hilbert.MeetsOpen K M.factorCount M.ambientDimension q.1.asIdeal U) := fun h => hu h.2
      rw [if_neg hn, if_pos ⟨hr, hdim q.1.asIdeal q.2 hr⟩]
      exact mul_nonneg (Nat.cast_nonneg _)
        (PrimaryComponentSupport.degreeValue_nonneg M _
          (Hilbert.minimalPrime_homogeneous M I q.1.asIdeal hI q.2) d)
  · rw [if_neg (fun h => hr h.1), if_neg (fun h => hr h.1)]

end PhilipponMultiplicity.SectionThreeSupport

theorem solution
    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
(I : Ideal M.CoordinateRing)
    (hI : IsMultihomogeneousIdeal M I)
    (hdim : ∀ q ∈ I.minimalPrimes,
      Hilbert.IsRelevant K M.factorCount M.ambientDimension q →
      idealDimension M q = idealDimension M I)
    (U : MaximalOpenLocus M) (d : M.FactorIndex → ℕ) :
    componentHilbertSum M I U d ≤ idealDegreeValue M I d := by
  exact PhilipponMultiplicity.SectionThreeSupport.componentSum_le_degreeValue_of_equidimensional M I hI hdim U d
