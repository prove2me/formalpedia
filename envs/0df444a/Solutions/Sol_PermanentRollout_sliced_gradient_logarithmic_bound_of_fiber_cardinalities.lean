-- Prove2me | solution 1 for PermanentRollout.sliced_gradient_logarithmic_bound_of_fiber_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/4550d873-51a5-4e0b-b097-d06c7e57c962

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_homogeneous_logarithmic_product_bound_of_fiber_cardinalities

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k d q cardinality : ℕ} (hd : 2 ≤ d)
    (hdegree : (d - 1) ^ k ≤ cardinality)
    (hbezout : cardinality ≤ 2 ^ q) :
    (k : ℝ) * Real.logb 2 ((d : ℝ) - 1) ≤ (q : ℝ) := by
  have he : 0 < d - 1 := by omega
  have hcast : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ d)]
    norm_num
  simpa [hcast] using
    (homogeneous_logarithmic_product_bound_of_fiber_cardinalities
      (k := k) (e := d - 1) (q := q) he hdegree hbezout)
end PermanentRollout
