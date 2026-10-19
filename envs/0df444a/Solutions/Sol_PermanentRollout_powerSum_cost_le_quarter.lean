-- Prove2me | solution 1 for PermanentRollout.powerSum_cost_le_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/96511420-25d0-4580-a8b5-22bb601ba4e8

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ}
    (hscale : 4 * powerSumParameter d ≤ blockWidth d * blockColumns n d) :
    blockCount n d * powerSumParameter d ≤ blockVariables n d / 4 := by
  apply (Nat.le_div_iff_mul_le (by omega : 0 < (4 : ℕ))).2
  have hmul := Nat.mul_le_mul_left (blockCount n d) hscale
  simpa [blockVariables, blockRows, mul_assoc, mul_comm, mul_left_comm] using hmul
end PermanentRollout
