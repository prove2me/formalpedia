-- Prove2me | solution 1 for PermanentRollout.exists_blockTree_leafList
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/f47952d7-470c-40f1-ab45-4ec126e4c539

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution {ι : Type*}
    (labels : List ι) (hne : labels ≠ []) :
    ∃ tree : BlockTree ι, tree.leafList = labels := by
  induction labels with
  | nil => exact (hne rfl).elim
  | cons head tail ih =>
      by_cases htail : tail = []
      · subst tail
        exact ⟨BlockTree.leaf head, rfl⟩
      · obtain ⟨tree, htree⟩ := ih htail
        exact ⟨BlockTree.branch (BlockTree.leaf head) tree, by
          simp [htree]⟩
end PermanentRollout
