-- Prove2me | solution 1 for PermanentRollout.squareFreeExponent_sub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/a46870aa-1458-448e-831e-20d901197fba

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (target removed : Finset ι) :
    squareFreeExponent target - squareFreeExponent removed =
      squareFreeExponent (target \ removed) := by
  classical
  ext i
  by_cases htarget : i ∈ target <;>
    by_cases hremoved : i ∈ removed <;>
      simp [Finsupp.tsub_apply, squareFreeExponent_apply,
        htarget, hremoved]
end PermanentRollout
