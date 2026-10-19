-- Prove2me | solution 1 for PermanentRollout.square_le_six_mul_blockVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/1462bff7-40ca-4330-b017-982bc470560c

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_le_three_mul_blockRows
import Theorems.Thm_PermanentRollout_le_two_mul_blockColumns

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : n ^ 2 ≤ 6 * blockVariables n d := by
  have hproduct := Nat.mul_le_mul (le_three_mul_blockRows hd hn)
    (le_two_mul_blockColumns n d)
  calc
    n ^ 2 = n * n := by rw [pow_two]
    _ ≤ (3 * blockRows n d) * (2 * blockColumns n d) := hproduct
    _ = 6 * blockVariables n d := by
      unfold blockVariables
      ring
end PermanentRollout
