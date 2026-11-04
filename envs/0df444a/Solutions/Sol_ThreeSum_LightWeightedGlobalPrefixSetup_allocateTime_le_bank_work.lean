-- Prove2me | solution 1 for ThreeSum.LightWeightedGlobalPrefixSetup.allocateTime_le_bank_work
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:05:28.165677+00:00
-- url     : https://prove2.me/submissions/26622b50-f88b-4ddd-9a3d-ec97b7d9dd90

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_EnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightNatPower
import Definitions.Def_Submission_Weighted_BankCanonical
import Definitions.Def_Submission_Weighted_Global_DimensionBounds
import Definitions.Def_Submission_Weighted_Global_LightTernaryPrefixSetup
import Theorems.Thm_ThreeSum_LightWeightedGlobalPrefixSetup_allocateTime_bound

set_option autoImplicit false
open ThreeSum ThreeSum.LightWeightedGlobalPrefixSetup
open Light LightSubsetAddress WeightedAddresses WeightedBankEnumeration
open WeightedGlobalLocalParameters WeightedGlobalDimensionBounds
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightWeightedGlobalPrefixSetup
theorem _root_.solution {m : ℕ} (hm : 0<m) (j : ℕ) :
    allocateTime m j≤2000*(N m j+1)*(nb m j+1) :=by
  have hjm : j≤j*m :=Nat.le_mul_of_pos_right _ hm
  have hjN : j≤N m j :=by unfold N; omega
  have hh:=allocateTime_bound m j
  nlinarith only [hh,hjN,Nat.zero_le (N m j*nb m j),Nat.zero_le (nb m j)]
end ThreeSum.LightWeightedGlobalPrefixSetup
