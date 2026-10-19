-- Prove2me | solution 1 for PermanentRollout.blockVariables_eq_four_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/302f9d35-bba6-4c1a-aea1-cb54db7ddf35

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution (n d : ℕ) :
    blockVariables n d = 4 * (blockCount n d * blockColumns n d * d) := by
  simp [blockVariables, blockRows, blockWidth, mul_assoc, mul_comm, mul_left_comm]
end PermanentRollout
