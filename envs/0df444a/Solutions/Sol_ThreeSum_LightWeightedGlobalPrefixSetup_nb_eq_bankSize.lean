-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixSetup.nb_eq_bankSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:58:03.603741+00:00
-- url     : https://prove2.me/submissions/23daad5e-1b84-4a38-9dee-70a0d79e72e5

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_dimensions
import Theorems.Thm_ThreeSum_TernaryBankEnumeration_codes_length_eq_bank_card
import Theorems.Thm_ThreeSum_WeightedBankEnumeration_codes_length_eq_bank_card


set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution (m j : ℕ) : nb m j=bankSize m j :=by
  unfold nb bankSize
  rw [codes_length_eq_bank_card]
  rw [(dimensions m j).1,(dimensions m j).2.1]
end ThreeSum.LightWeightedGlobalPrefixSetup
