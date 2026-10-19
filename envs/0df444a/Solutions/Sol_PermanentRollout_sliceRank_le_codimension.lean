-- Prove2me | solution 1 for PermanentRollout.sliceRank_le_codimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/8e053e20-61a1-4c60-bbff-39fbe2d8b7de

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_twice_criticalDimension_lt_blockVariables

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d dimension : ℕ}
    (hd : 3 ≤ d) (hn : 6 * blockWidth d ≤ n)
    (hscale : 4 * powerSumParameter d ≤ blockWidth d * blockColumns n d)
    (hdimension : dimension ≤ blockCount n d *
      (powerSumParameter d + blockColumns n d * (d - 2))) :
    sliceRank n d ≤ blockVariables n d - dimension := by
  have hhalf := twice_criticalDimension_lt_blockVariables hd hn hscale hdimension
  have hfloor := Nat.div_mul_le_self (blockVariables n d) 4
  unfold sliceRank
  omega
end PermanentRollout
