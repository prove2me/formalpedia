-- Prove2me | solution 1 for PermanentRollout.blockVariables_le_eight_mul_sliceRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/73d4caab-caa0-41ac-a2a5-e9d0bf6cc9a6

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ}
    (hm : 8 ≤ blockVariables n d) :
    blockVariables n d ≤ 8 * sliceRank n d := by
  unfold sliceRank
  have hrem := Nat.mod_lt (blockVariables n d) (by omega : 0 < (4 : ℕ))
  have hdecomp := Nat.mod_add_div (blockVariables n d) 4
  omega
end PermanentRollout
