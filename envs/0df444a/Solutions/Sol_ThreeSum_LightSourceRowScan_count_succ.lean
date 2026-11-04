-- Prove2me | solution 1 for ThreeSum.LightSourceRowScan.count_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:36.867017+00:00
-- url     : https://prove2.me/submissions/27ac280a-d62a-456b-9373-ccab3d5f3d7f

import Definitions.Def_Submission_ThreeSum_LightArray
import Definitions.Def_Submission_ThreeSum_LightMaskBits
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightSourceRowScan

set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceRowScan
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceRowScan
theorem _root_.solution (bits : ℕ → ℕ) (n : ℕ) : count bits (n+1)=count bits n+bits n :=
  Finset.sum_range_succ _ _
end ThreeSum.LightSourceRowScan
