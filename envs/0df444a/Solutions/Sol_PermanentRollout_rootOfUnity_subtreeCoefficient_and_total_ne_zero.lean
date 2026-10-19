-- Prove2me | solution 1 for PermanentRollout.rootOfUnity_subtreeCoefficient_and_total_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/442986ce-7f75-4e0e-acea-0e5312d68b66

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_rootOfUnity_node_coefficient_ne_zero
import Theorems.Thm_PermanentRollout_rootOfUnity_node_coefficient_add_one_ne_zero
import Theorems.Thm_PermanentRollout_subtreeCoefficient_and_total_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
namespace PermanentRollout
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] {d : ℕ} (hd : 0 < d)
    (tree : BlockTree ι) (hnodup : tree.leafList.Nodup) :
    let lam : ℂ := (-1 : ℂ) ^ (d + 1) * (2 : ℂ) ^ d
    (∀ i ∈ tree.leaves, subtreeCoefficient lam tree i ≠ 0) ∧
      subtreeCoefficientTotal lam tree ≠ 0 := by
  dsimp
  exact subtreeCoefficient_and_total_ne_zero _
    (rootOfUnity_node_coefficient_ne_zero d)
    (rootOfUnity_node_coefficient_add_one_ne_zero hd) tree hnodup
end PermanentRollout
