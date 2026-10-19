-- Prove2me | solution 1 for PermanentRollout.treeQuotientLinearForm_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:09.567922+00:00
-- url     : https://prove2.me/submissions/36740583-9618-4589-a1cd-e4da4fff49f5

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_block
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_add
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_smul
import Theorems.Thm_PermanentRollout_treeQuotientLinearForm_sum

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {r : ℕ} {ι : Type*}
    [DecidableEq ι] (blocks : ι → Finset (Fin r))
    (left right : BlockTree ι) (ζ : ℂ) (j : ℕ) :
    treeQuotientLinearForm (treeNodeVector blocks left right ζ j) =
      (∑ i ∈ left.leaves, squareZeroBlockSum r (blocks i)) +
        algebraMap ℂ (SquareZeroAlgebra r) (2 * ζ ^ j) *
          (∑ i ∈ right.leaves, squareZeroBlockSum r (blocks i)) := by
  unfold treeNodeVector
  rw [treeQuotientLinearForm_add,
    treeQuotientLinearForm_smul,
    treeQuotientLinearForm_sum,
    treeQuotientLinearForm_sum]
  simp only [treeQuotientLinearForm_block]
end PermanentRollout
