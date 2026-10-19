-- Prove2me | solution 1 for PermanentRollout.homogeneous_logarithmic_product_bound_of_fiber_cardinalities
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/85c9ab36-35d2-4751-a9d6-c412c9b7be40

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k e q cardinality : ℕ} (he : 0 < e)
    (hdegree : e ^ k ≤ cardinality)
    (hbezout : cardinality ≤ 2 ^ q) :
    (k : ℝ) * Real.logb 2 (e : ℝ) ≤ (q : ℝ) := by
  have hpower : e ^ k ≤ 2 ^ q := hdegree.trans hbezout
  have hreal : (e : ℝ) ^ k ≤ (2 : ℝ) ^ q := by
    exact_mod_cast hpower
  have he_real : 0 < (e : ℝ) := by
    exact_mod_cast he
  have hlog := Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) (pow_pos he_real k) hreal
  simpa [Real.logb_pow] using hlog
end PermanentRollout
