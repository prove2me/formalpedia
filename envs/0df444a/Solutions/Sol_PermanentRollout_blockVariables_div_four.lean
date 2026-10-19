-- Prove2me | solution 1 for PermanentRollout.blockVariables_div_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/e653f423-27be-4b88-8803-a287d9615738

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_blockVariables_eq_four_mul

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution (n d : ℕ) :
    blockVariables n d / 4 = blockCount n d * blockColumns n d * d := by
  rw [blockVariables_eq_four_mul]
  simp
end PermanentRollout
