-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlockCommonFactor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/5f3f00c5-9b32-45e9-adee-283fc19e3507

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution (b t s d : ℕ) :
    sourceTreeBlockCommonFactor b t s d ≠ 0 := by
  unfold sourceTreeBlockCommonFactor
  exact mul_ne_zero
    (mul_ne_zero
      (by exact_mod_cast (s - d).factorial_ne_zero)
      (by exact_mod_cast (t - d).factorial_ne_zero))
    (pow_ne_zero _ (by exact_mod_cast t.factorial_ne_zero))
end PermanentRollout
