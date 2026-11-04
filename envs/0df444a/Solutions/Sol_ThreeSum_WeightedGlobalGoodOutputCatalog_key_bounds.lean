-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.key_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:20:22.841685+00:00
-- url     : https://prove2.me/submissions/8f839898-8b81-4012-acd3-3da860a80e57

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.WeightedGlobalGoodOutputCatalog
theorem _root_.solution (maps : I → Weight m p) (r : Record m I) :
    0≤key maps r ∧ key maps r<(p : ℤ) := by
  unfold key
  exact ⟨Int.ofNat_zero_le _,by exact_mod_cast ZMod.val_lt (native (maps r.1) r.2)⟩
end ThreeSum.WeightedGlobalGoodOutputCatalog
