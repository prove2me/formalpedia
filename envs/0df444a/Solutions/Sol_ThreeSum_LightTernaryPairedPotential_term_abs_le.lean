-- Prove2me | solution 1 for ThreeSum.LightTernaryPairedPotential.term_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:40:29.349796+00:00
-- url     : https://prove2.me/submissions/bde17110-3f29-4c2c-affc-159560a271f0

import Definitions.Def_Submission_ThreeSum_TernaryPairedColumnEnumeration
import Definitions.Def_Submission_ThreeSum_LightWeightRow
import Definitions.Def_Submission_ThreeSum_LightTernaryPairedPotential
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_tensorIndex_lt
import Theorems.Thm_ThreeSum_LightTernaryPairedPolynomial_value_abs_le
import Theorems.Thm_ThreeSum_WeightEnumeration_digit_lt


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernaryPairedPotential
open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators
namespace ThreeSum.LightTernaryPairedPotential
theorem _root_.solution (m base Λ : ℕ) (μ : ℕ → ℤ) (U : ℤ) (hU : 0≤U) (hΛ : 1≤Λ)
    (hT : ∀ k<Λ^4, |μ (base+k)|≤U) (i : ℕ) :
    |term m base Λ μ i|≤(polynomial m).bound U := by
  apply value_abs_le _ U hU
  intro q
  exact hT _ (tensorIndex_lt
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))
end ThreeSum.LightTernaryPairedPotential
