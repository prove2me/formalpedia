-- Prove2me | solution 1 for PermanentRollout.squareFreeExponent_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/75015073-da3f-43d5-a779-8fa43a5b0adb

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} (rows : Finset ι) :
    (squareFreeExponent rows).sum (fun _ n => n) = rows.card := by
  classical
  simp [Finsupp.sum, squareFreeExponent_support,
    squareFreeExponent_apply]
end PermanentRollout
