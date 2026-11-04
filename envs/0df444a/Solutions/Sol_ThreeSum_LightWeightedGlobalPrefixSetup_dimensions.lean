-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixSetup.dimensions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:51:55.662361+00:00
-- url     : https://prove2.me/submissions/48f81fee-b1ed-4e83-8000-0fa8fbb5cd1c

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
namespace ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution (m j : ℕ) :
    N m j=fixedLength (j*m) ∧ T m j=bankCut m j ∧ T m j≤ 1025*N m j := by
  unfold N T fixedLength bankCut
  constructor
  · rfl
  constructor
  · ring
  · omega
end ThreeSum.LightWeightedGlobalPrefixSetup
