-- Prove2me | solution 1 for ThreeSum.TernaryEntropyRates.typeCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:02:45.497451+00:00
-- url     : https://prove2.me/submissions/cca8f82c-ec4c-4f61-9a96-a9c07c59902b

import Definitions.Def_Submission_ThreeSum_TernaryParameters
import Definitions.Def_Submission_ThreeSum_TernaryCoverScale
import Definitions.Def_Submission_ThreeSum_TernaryTypeCardinality
import Definitions.Def_Submission_ThreeSum_TernaryEntropyRates

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale
set_option maxRecDepth 10000
namespace ThreeSum.TernaryEntropyRates
theorem _root_.solution {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by
  unfold typeCount
  exact Nat.mul_pos (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
    (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
end ThreeSum.TernaryEntropyRates
