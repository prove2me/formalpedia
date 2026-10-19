-- Prove2me | solution 1 for PermanentRollout.subtreeCoefficient_branch_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/dd3253a9-dd52-45ac-8367-c156622e2417

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_subtreeCoefficient_eq_zero_of_not_mem

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    (lam : ℂ) {left right : BlockTree ι}
    (hdisj : Disjoint left.leaves right.leaves) {i : ι}
    (hi : i ∈ right.leaves) :
    subtreeCoefficient lam (.branch left right) i =
      subtreeCoefficientTotal lam left * subtreeCoefficient lam right i := by
  have hnot : i ∉ left.leaves :=
    fun h => (Finset.disjoint_left.mp hdisj) h hi
  simp [subtreeCoefficient, subtreeCoefficientTotal,
    subtreeCoefficient_eq_zero_of_not_mem lam left hnot]
end PermanentRollout
