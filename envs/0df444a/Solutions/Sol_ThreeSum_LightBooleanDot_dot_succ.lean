-- Prove2me | solution 1 for ThreeSum.LightBooleanDot.dot_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:26:45.004409+00:00
-- url     : https://prove2.me/submissions/e1d0b550-8eba-4473-a067-38cad147e3c6

import Definitions.Def_Submission_ThreeSum_LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Definitions.Def_Submission_ThreeSum_LightBooleanDot

set_option autoImplicit false
open ThreeSum ThreeSum.LightBooleanDot
open Light Finset
open scoped BigOperators
namespace ThreeSum.LightBooleanDot
theorem _root_.solution (f g : ℕ → ℕ) (j : ℕ) :
    dot f g (j+1) = dot f g j + f j*g j := sum_range_succ _ _
end ThreeSum.LightBooleanDot
