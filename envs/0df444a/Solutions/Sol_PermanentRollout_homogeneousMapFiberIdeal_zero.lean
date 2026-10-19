-- Prove2me | solution 1 for PermanentRollout.homogeneousMapFiberIdeal_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:03.257302+00:00
-- url     : https://prove2.me/submissions/9c339c70-5c82-46d4-80c4-3f21a29d9b12

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {ι : Type*}
    (F : ι → MvPolynomial ι ℂ) :
    homogeneousMapFiberIdeal F 0 = homogeneousMapIdeal F := by
  simp [homogeneousMapFiberIdeal, homogeneousMapIdeal]
end PermanentRollout
