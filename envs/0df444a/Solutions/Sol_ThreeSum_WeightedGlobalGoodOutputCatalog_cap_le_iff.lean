-- Prove2me | solution 1 for ThreeSum.WeightedGlobalGoodOutputCatalog.cap_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:32.745547+00:00
-- url     : https://prove2.me/submissions/a32c600d-0680-4c87-a349-8b36cef37fa2

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
theorem _root_.solution (τ C : ℕ) : cap m p τ≤C ↔
    partitionLoss (2380004124000*m) (292746547000*m)*p*τ≤Rbar m*C := by
  exact ceilDiv_le_iff_le_mul (by unfold Rbar; positivity)
end ThreeSum.WeightedGlobalGoodOutputCatalog
