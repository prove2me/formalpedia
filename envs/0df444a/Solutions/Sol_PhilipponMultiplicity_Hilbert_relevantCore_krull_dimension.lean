-- Prove2me | solution 1 for PhilipponMultiplicity.Hilbert.relevantCore_krull_dimension
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-27T07:07:58.721771+00:00
-- url     : https://prove2.me/submissions/183fbaf3-56b7-4559-88ac-116c7b30a14b

import Definitions.Def_PhilipponMultiplicity_SectionThreeSupport
import Theorems.Thm_PhilipponMultiplicity_Hilbert_exists_relevant_minimalPrime_dimension_eq
import Theorems.Thm_Ideal_ringKrullDim_quotient_finite_iInf
import Theorems.Thm_PhilipponMultiplicity_Hilbert_relevant_prime_krull_dimension_formula
import Theorems.Thm_PhilipponMultiplicity_Hilbert_minimalPrime_homogeneous
import Theorems.Thm_PhilipponMultiplicity_Hilbert_idealDimension_antitone

set_option autoImplicit false
open scoped BigOperators
open MvPolynomial PhilipponMultiplicity PhilipponMultiplicity.SectionThree
open PhilipponMultiplicity.SectionThreeSupport PhilipponMultiplicity.Hilbert
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace PhilipponMultiplicity.Hilbert
open SectionThree SectionThreeSupport
variable {K : Type*} [Field K] (M : MultiProjectiveSpace K)

/-- Reduction of the relevant-core dimension comparison to its prime case.
The prime comparison remains an explicit hypothesis of this reduction. -/
theorem relevantCore_krull_dimension_of_prime_formula
    (hprime : ∀ q : Ideal M.CoordinateRing, q.IsPrime →
      IsMultihomogeneousIdeal M q → IsRelevant K M.factorCount M.ambientDimension q →
      ringKrullDim (M.CoordinateRing ⧸ q) =
        ((idealDimension M q + M.factorCount : ℕ) : WithBot ℕ∞))
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) :
    ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
      ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞) := by
  classical
  unfold relevantRadicalCore
  rw [Ideal.ringKrullDim_quotient_finite_iInf]
  apply le_antisymm
  · refine iSup_le fun q => ?_
    by_cases hrel : IsRelevant K M.factorCount M.ambientDimension q.val.asIdeal
    · rw [if_pos hrel, hprime q.val.asIdeal q.val.isPrime
        (minimalPrime_homogeneous M I q.val.asIdeal hI q.property) hrel]
      exact_mod_cast Nat.add_le_add_right (idealDimension_antitone M I q.val.asIdeal hI
        (minimalPrime_homogeneous M I q.val.asIdeal hI q.property) q.property.1.2)
        M.factorCount
    · rw [if_neg hrel, ringKrullDim_eq_bot_of_subsingleton]
      exact bot_le
  · obtain ⟨q, hq, hrel, hdim⟩ := exists_relevant_minimalPrime_dimension_eq M I hI hNontrivial
    let q₀ : MinimalComponent K M.factorCount M.ambientDimension I := ⟨⟨q, hq.1.1⟩, hq⟩
    have hvalue : ringKrullDim (M.CoordinateRing ⧸
        (if IsRelevant K M.factorCount M.ambientDimension q₀.val.asIdeal then
          q₀.val.asIdeal else ⊤)) =
        ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞) := by
      change ringKrullDim (M.CoordinateRing ⧸ (if IsRelevant K M.factorCount
        M.ambientDimension q then q else ⊤)) = _
      rw [if_pos hrel, hprime q hq.1.1 (minimalPrime_homogeneous M I q hI hq) hrel, hdim]
    rw [← hvalue]
    exact le_iSup (fun q : MinimalComponent K M.factorCount M.ambientDimension I =>
      ringKrullDim (M.CoordinateRing ⧸ if IsRelevant K M.factorCount M.ambientDimension
        q.val.asIdeal then q.val.asIdeal else ⊤)) q₀

end PhilipponMultiplicity.Hilbert

end

theorem solution    {K : Type*} [Field K] (M : MultiProjectiveSpace K)
    (I : Ideal M.CoordinateRing) (hI : IsMultihomogeneousIdeal M I)
    (hNontrivial : IsNontrivialIdeal M I) :
    ringKrullDim (M.CoordinateRing ⧸ relevantRadicalCore M I) =
      ((idealDimension M I + M.factorCount : ℕ) : WithBot ℕ∞) := by
  exact PhilipponMultiplicity.Hilbert.relevantCore_krull_dimension_of_prime_formula M
    (PhilipponMultiplicity.Hilbert.relevant_prime_krull_dimension_formula M) I hI hNontrivial
