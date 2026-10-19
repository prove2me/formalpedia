-- Prove2me | solution 1 for PermanentRollout.sourceTreeBlockWeight_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:10.343013+00:00
-- url     : https://prove2.me/submissions/9b8cdfbf-6e79-4953-a3cc-9bf19bb8a8ec

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_rootOfUnity_subtreeCoefficient_and_total_ne_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {b d : ℕ} (hd : 0 < d)
    (tree : BlockTree (Fin b))
    (hnodup : tree.leafList.Nodup)
    (hleaves : tree.leaves = Finset.univ) :
    ∀ h : Fin b, sourceTreeBlockWeight b d tree h ≠ 0 := by
  intro h
  exact (rootOfUnity_subtreeCoefficient_and_total_ne_zero
    hd tree hnodup).1 h (by simp [hleaves])
end PermanentRollout
