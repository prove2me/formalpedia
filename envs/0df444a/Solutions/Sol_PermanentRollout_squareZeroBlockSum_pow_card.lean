-- Prove2me | solution 1 for PermanentRollout.squareZeroBlockSum_pow_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/0c08965a-310e-4067-8d3a-28af05288acb

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
    squareZeroBlockSum r block ^ block.card =
      (block.card.factorial : SquareZeroAlgebra r) *
        ∏ i ∈ block, squareZeroVariable r i := by
  exact (square_zero_sum_pow_card_and_succ block (squareZeroVariable r)
    (fun i _ => squareZeroVariable_sq r i)).1
end PermanentRollout
