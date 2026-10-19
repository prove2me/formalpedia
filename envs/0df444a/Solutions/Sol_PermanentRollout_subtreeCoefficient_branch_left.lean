-- Prove2me | solution 1 for PermanentRollout.subtreeCoefficient_branch_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/23a62686-9002-48d6-8296-8bac0cfbd775

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
    (hi : i ∈ left.leaves) :
    subtreeCoefficient lam (.branch left right) i =
      lam * subtreeCoefficientTotal lam right * subtreeCoefficient lam left i := by
  have hnot : i ∉ right.leaves :=
    fun h => (Finset.disjoint_left.mp hdisj) hi h
  simp [subtreeCoefficient, subtreeCoefficientTotal,
    subtreeCoefficient_eq_zero_of_not_mem lam right hnot]
end PermanentRollout
