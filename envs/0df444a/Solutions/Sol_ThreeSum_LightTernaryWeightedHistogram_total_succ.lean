-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedHistogram.total_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:22:09.26142+00:00
-- url     : https://prove2.me/submissions/46bbd439-2be6-4074-bce7-03816b445750

import Definitions.Def_Submission_ThreeSum_LightHistogram
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedHistogram

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedHistogram
open Light Finset
open scoped BigOperators
set_option maxHeartbeats 2000000
namespace ThreeSum.LightTernaryWeightedHistogram
theorem _root_.solution (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n : ℕ) :
    total key weight r (n+1)=total key weight r n+
      if key n=r then weight n else 0 := by
  unfold total
  rw [sum_range_succ]
end ThreeSum.LightTernaryWeightedHistogram
