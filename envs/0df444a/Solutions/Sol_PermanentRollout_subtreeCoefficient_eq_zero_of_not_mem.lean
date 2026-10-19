-- Prove2me | solution 1 for PermanentRollout.subtreeCoefficient_eq_zero_of_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/9ef1874e-fef0-4f5c-a93b-3f7d25d433db

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (lam : ℂ) (tree : BlockTree ι) {i : ι} (hi : i ∉ tree.leaves) :
    subtreeCoefficient lam tree i = 0 := by
  induction tree with
  | leaf label =>
    simp_all
  | branch left right left_ih right_ih =>
    have hi_left : i ∉ left.leaves := by
      intro h
      exact hi (Finset.mem_union_left _ h)
    have hi_right : i ∉ right.leaves := by
      intro h
      exact hi (Finset.mem_union_right _ h)
    simp [subtreeCoefficient, left_ih hi_left, right_ih hi_right]
end PermanentRollout
