-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.native_fiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:50:36.946363+00:00
-- url     : https://prove2.me/submissions/cc150372-7169-4784-b5e2-00068ec3621b

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_Global_TernaryLiteralOutputCap
import Definitions.Def_Submission_Weighted_Global_TernaryCoverGoodMaps
import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCodeSemantics
import Mathlib.Algebra.Order.Floor.Div
import Definitions.Def_Submission_Weighted_Global_TernaryGoodOutputCatalog
import Theorems.Thm_ThreeSum_WeightedGlobalGoodOutputCatalog_fixed_output_cap

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalGoodOutputCatalog
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open WeightedGlobalCoverGoodMaps TernaryCoverFibers WeightedGlobalLocalParameters WeightedGlobalPartitionCount
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {m p : ℕ} [Fact p.Prime]
namespace ThreeSum.WeightedGlobalGoodOutputCatalog
theorem _root_.solution (τ : ℕ) (w : Weight m p) (hgood : w∉rawBadMaps m p τ) (o : ZMod p) :
    outputFiberCount (native w) o≤cap m p τ := by
  have hR : 0<Rbar m := by unfold Rbar; positivity
  have hA := fixed_output_cap τ w hgood o
  have hceil : partitionLoss (2380004124000*m) (292746547000*m)*p*τ≤Rbar m*cap m p τ := by
    exact (ceilDiv_le_iff_le_mul hR).mp le_rfl
  nlinarith
end ThreeSum.WeightedGlobalGoodOutputCatalog
