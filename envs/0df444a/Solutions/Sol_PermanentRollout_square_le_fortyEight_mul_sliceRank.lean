-- Prove2me | solution 1 for PermanentRollout.square_le_fortyEight_mul_sliceRank
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:06.641753+00:00
-- url     : https://prove2.me/submissions/53d9b4b4-917e-4086-ad88-86cb9508f61a

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_square_le_six_mul_blockVariables
import Theorems.Thm_PermanentRollout_eight_le_blockVariables
import Theorems.Thm_PermanentRollout_blockVariables_le_eight_mul_sliceRank

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
namespace PermanentRollout
theorem _root_.solution {n d : ℕ} (hd : 3 ≤ d)
    (hn : 6 * blockWidth d ≤ n) : n ^ 2 ≤ 48 * sliceRank n d := by
  have hmass := square_le_six_mul_blockVariables hd hn
  have height := blockVariables_le_eight_mul_sliceRank
    (eight_le_blockVariables hd hn)
  omega
end PermanentRollout
