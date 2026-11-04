-- Prove2me | solution 1 for ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:25:00.487725+00:00
-- url     : https://prove2.me/submissions/343a1b2a-bc67-4bd6-930f-f26e9ec21891

import Definitions.Def_Submission_Weighted_BankEnumeration
import Definitions.Def_Submission_Weighted_NearBankEnumeration
import Definitions.Def_Submission_Weighted_FrozenQueryCost
import Definitions.Def_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_WeightedNearBankEnumeration_codes_length_gibbs


set_option autoImplicit false
open ThreeSum ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (nearWords Q D).card*z^D≤(1+z^512)^digitCount Q 1*(1+z^513+z^1025)^digitCount Q 2 := by
  have h := WeightedNearBankEnumeration.codes_length_gibbs Q D z hz hz1
  rwa [WeightedNearBankEnumeration.codes_length_eq_nearWords_card,
    WeightedFrozenQueryCost.polynomial_product_counts] at h
end ThreeSum.WeightedGlobalBank
