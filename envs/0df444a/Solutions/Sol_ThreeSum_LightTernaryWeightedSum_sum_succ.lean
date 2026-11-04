-- Prove2me | solution 1 for ThreeSum.LightTernaryWeightedSum.sum_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:30:32.322887+00:00
-- url     : https://prove2.me/submissions/ea42ec91-f379-4f6d-90d0-75cce96b874d

import Definitions.Def_Submission_ThreeSum_LightLookupSum
import Definitions.Def_Submission_ThreeSum_LightTernaryWeightedSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryWeightedSum
open Light Finset
namespace ThreeSum.LightTernaryWeightedSum
theorem _root_.solution (weights keys : ℕ → ℕ) (f : ℕ → ℤ) (j : ℕ) :
    sum weights keys f (j+1) = sum weights keys f j + (weights j : ℤ)*f (keys j) :=
  sum_range_succ _ _
end ThreeSum.LightTernaryWeightedSum
