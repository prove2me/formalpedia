-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank.nearWords_card_gibbs_counts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:23:19.478835+00:00
-- url     : https://prove2.me/submissions/879fe542-2bcf-4431-a9ee-fa1f698ddfa7

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_NearBankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_FrozenQueryCost
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_GlobalBank
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_gibbs
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_ThreeSum_TernaryNearBankEnumeration_codes_length_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankEnumeration_codes_length_gibbs
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedFrozenQueryCost_polynomial_product_counts
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_eq_nearWords_card
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedNearBankEnumeration_codes_length_gibbs


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
open TernaryJointType
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
theorem _root_.solution {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0≤z) (hz1 : z≤1) :
    (nearWords Q D).card*z^D≤(1+z^1369)^digitCount Q 1*(1+z^1371+z^2740)^digitCount Q 2 := by
  have h := WeightedNearBankEnumeration.codes_length_gibbs Q D z hz hz1
  rwa [WeightedNearBankEnumeration.codes_length_eq_nearWords_card,
    WeightedFrozenQueryCost.polynomial_product_counts] at h
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedGlobalBank
