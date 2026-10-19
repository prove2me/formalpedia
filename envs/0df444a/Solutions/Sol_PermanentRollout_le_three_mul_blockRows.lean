-- Prove2me | solution 1 for PermanentRollout.le_three_mul_blockRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/a6d8d46c-8672-462b-b55e-e6ef4fb1ba56

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : n ≤ 3 * blockRows n d := by
  have hden : 0 < 2 * blockWidth d := by
    simp only [blockWidth]
    omega
  have hrem := Nat.mod_lt n hden
  have hrows := three_mul_blockWidth_le_blockRows hd hn
  have hdecomp :
      n % (2 * blockWidth d) + 2 * blockRows n d = n := by
    simpa [blockRows, blockCount, mul_assoc, mul_comm, mul_left_comm] using
      Nat.mod_add_div n (2 * blockWidth d)
  omega
end PermanentRollout
