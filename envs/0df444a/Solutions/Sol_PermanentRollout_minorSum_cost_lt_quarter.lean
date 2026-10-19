-- Prove2me | solution 1 for PermanentRollout.minorSum_cost_lt_quarter
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/b52f6e3c-15c6-4ca9-832a-41c3dc3e776f

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockVariables_div_four

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) :
    blockCount n d * blockColumns n d * (d - 2) < blockVariables n d / 4 := by
  have hb : 0 < blockCount n d := by
    have hthree := three_le_blockCount hd hn
    omega
  have hs : 0 < blockColumns n d := by
    have hcolumns := degree_le_blockColumns n d
    omega
  rw [blockVariables_div_four]
  exact Nat.mul_lt_mul_of_pos_left (by omega : d - 2 < d) (Nat.mul_pos hb hs)
end PermanentRollout
