-- Prove2me | solution 1 for PermanentRollout.squareZeroBlockSum_pow_card_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/1046fadd-c305-42c8-97d0-b30499601fc5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_square_zero_sum_pow_card_and_succ

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution (r : ℕ) (block : Finset (Fin r)) :
    squareZeroBlockSum r block ^ (block.card + 1) = 0 := by
  exact (square_zero_sum_pow_card_and_succ block (squareZeroVariable r)
    (fun i _ => squareZeroVariable_sq r i)).2
end PermanentRollout
