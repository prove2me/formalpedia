-- Prove2me | solution 1 for PermanentRollout.twice_criticalDimension_lt_blockVariables
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/585b6714-faac-42f0-a27c-ceab4e2b367e

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_powerSum_cost_le_quarter
import Theorems.Thm_PermanentRollout_minorSum_cost_lt_quarter

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
    2 * dimension < blockVariables n d := by
  have hpower := powerSum_cost_le_quarter hscale
  have hminor := minorSum_cost_lt_quarter hd hn
  have hfloor := Nat.div_mul_le_self (blockVariables n d) 4
  have hbound : dimension ≤ blockCount n d * powerSumParameter d +
      blockCount n d * blockColumns n d * (d - 2) := by
    simpa [mul_add, mul_assoc] using hdimension
  omega
end PermanentRollout
