-- Prove2me | solution 1 for ThreeSum.LightSourceRowScan.hash_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:55:37.999808+00:00
-- url     : https://prove2.me/submissions/cb38540b-1ecb-4d47-adff-062882f1aed7

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
theorem _root_.solution (bits w0 w1 : ℕ → ℕ) (n : ℕ) :
    hash bits w0 w1 (n+1)=hash bits w0 w1 n+(if bits n=1 then w1 n else w0 n) :=
  Finset.sum_range_succ _ _
end ThreeSum.LightSourceRowScan
