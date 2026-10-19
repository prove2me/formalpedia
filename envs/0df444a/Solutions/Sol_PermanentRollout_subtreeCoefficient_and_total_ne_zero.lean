-- Prove2me | solution 1 for PermanentRollout.subtreeCoefficient_and_total_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/7c0c4cbe-2b8a-460f-93b5-708bf5b92dc2

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_BlockTree_disjoint_leaves_of_nodup
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_right
import Theorems.Thm_PermanentRollout_subtreeCoefficient_branch_left
import Theorems.Thm_PermanentRollout_subtreeCoefficientTotal_branch

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (lam : ℂ) (hlam : lam ≠ 0) (hlamone : 1 + lam ≠ 0)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup) :
    (∀ i ∈ tree.leaves, subtreeCoefficient lam tree i ≠ 0) ∧
      subtreeCoefficientTotal lam tree ≠ 0 := by
  induction tree with
  | leaf label =>
    simp
  | branch left right left_ih right_ih =>
    have hparts := List.nodup_append.mp hnodup
    have hdisj := BlockTree.disjoint_leaves_of_nodup hnodup
    obtain ⟨hleft_coeff, hleft_total⟩ := left_ih hparts.1
    obtain ⟨hright_coeff, hright_total⟩ := right_ih hparts.2.1
    constructor
    · intro i hi
      rcases Finset.mem_union.mp hi with hi_left | hi_right
      · rw [subtreeCoefficient_branch_left lam hdisj hi_left]
        exact mul_ne_zero (mul_ne_zero hlam hright_total)
          (hleft_coeff i hi_left)
      · rw [subtreeCoefficient_branch_right lam hdisj hi_right]
        exact mul_ne_zero hleft_total (hright_coeff i hi_right)
    · rw [subtreeCoefficientTotal_branch lam hdisj]
      exact mul_ne_zero (mul_ne_zero hlamone hleft_total) hright_total
end PermanentRollout
