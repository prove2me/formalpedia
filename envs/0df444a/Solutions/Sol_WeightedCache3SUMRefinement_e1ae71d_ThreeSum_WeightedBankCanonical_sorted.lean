-- Prove2me | solution 1 for WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical.sorted
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-04T10:20:10.878055+00:00
-- url     : https://prove2.me/submissions/12c8cbab-d70f-435f-8126-91c6471d6754

import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankStageModel
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankEnumeration
import Definitions.Def_WeightedCache3SUMRefinement_e1ae71d_Submission_Weighted_BankCanonical
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedBankCanonical_address_word
import Theorems.Thm_ThreeSum_TernaryAddresses_codes_strictly_sorted
import Theorems.Thm_WeightedCache3SUMRefinement_e1ae71d_ThreeSum_WeightedAddresses_codes_strictly_sorted


set_option autoImplicit false
open WeightedCache3SUMRefinement_e1ae71d
open _root_.ThreeSum
open WeightedCache3SUMRefinement_e1ae71d.ThreeSum WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical
open ThreeSum.TernaryJointType ThreeSum.WeightedEnumeration
open ThreeSum.WeightedAddresses ThreeSum.WeightedBankEnumeration ThreeSum.WeightedBankStageModel
open ThreeSum.TernaryCodeSemantics
set_option maxHeartbeats 2000000
namespace WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical
theorem _root_.solution (N T : ℕ) : ∀ j k, j<k → k<(codes N T).length →
    address ((enumeration N T).word j)<address ((enumeration N T).word k) := by
  intro j k hj hk
  change address (word N T j)<address (word N T k)
  rw [address_word (by omega),address_word hk]
  exact List.pairwise_iff_getElem.mp (codes_strictly_sorted N T) j k (by omega) hk hj
end WeightedCache3SUMRefinement_e1ae71d.ThreeSum.WeightedBankCanonical
