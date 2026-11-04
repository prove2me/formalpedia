-- Prove2me | solution 1 for ThreeSum.LightLookupSum.prefixSum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:17:35.059421+00:00
-- url     : https://prove2.me/submissions/4ee1a199-4cb9-418b-916e-8d46762f2bdc

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightLookupSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightLookupSum
open Light Finset
open scoped BigOperators
namespace ThreeSum.LightLookupSum
theorem _root_.solution (f key : ℕ → ℕ) (j : ℕ) :
    prefixSum f key (j+1) = prefixSum f key j + f (key j) := by
  exact sum_range_succ _ _
end ThreeSum.LightLookupSum
