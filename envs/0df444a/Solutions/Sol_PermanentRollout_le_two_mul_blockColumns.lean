-- Prove2me | solution 1 for PermanentRollout.le_two_mul_blockColumns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/6b2c17b1-69bc-4a67-ba02-04ac48e51e07

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution (n d : ℕ) : n ≤ 2 * blockColumns n d := by
  have hrows := two_mul_blockRows_le n d
  unfold blockColumns
  omega
end PermanentRollout
