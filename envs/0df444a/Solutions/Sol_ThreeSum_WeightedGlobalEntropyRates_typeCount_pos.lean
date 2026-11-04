-- Prove2me | solution 1 for ThreeSum.WeightedGlobalEntropyRates.typeCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:47:42.434078+00:00
-- url     : https://prove2.me/submissions/57e8b0cc-be12-4fb2-a8bd-c16f5344b129

import Definitions.Def_Submission_Weighted_GlobalBank
import Definitions.Def_Submission_Weighted_GlobalParameters
import Definitions.Def_Submission_Weighted_Global_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_Weighted_Global_TernaryEntropyRates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.WeightedGlobalEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal WeightedGlobalLocalParameters WeightedGlobalCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.WeightedGlobalEntropyRates
theorem _root_.solution {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by
  unfold typeCount
  exact Nat.mul_pos (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
    (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
end ThreeSum.WeightedGlobalEntropyRates
