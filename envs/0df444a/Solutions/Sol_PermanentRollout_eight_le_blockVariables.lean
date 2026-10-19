-- Prove2me | solution 1 for PermanentRollout.eight_le_blockVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/4e49d165-5dc7-499a-9029-ec261d286a63

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : 8 ≤ blockVariables n d := by
  have hdegrees := Nat.mul_le_mul (degree_le_blockRows hd hn)
    (degree_le_blockColumns n d)
  have hsquare := Nat.mul_le_mul hd hd
  unfold blockVariables
  omega
end PermanentRollout
