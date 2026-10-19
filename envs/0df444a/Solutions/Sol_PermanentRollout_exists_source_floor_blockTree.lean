-- Prove2me | solution 1 for PermanentRollout.exists_source_floor_blockTree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:11.481307+00:00
-- url     : https://prove2.me/submissions/5594349a-4d63-493b-92b7-edc9dd0923c9

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_exists_blockTree_leafList

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {n d : ℕ} (hd : 3 ≤ d) (hn : 6 * blockWidth d ≤ n) :
    ∃ tree : BlockTree (Fin (blockCount n d)),
      tree.leafList.Nodup ∧ tree.leaves = Finset.univ := by
  classical
  let labels : List (Fin (blockCount n d)) :=
    (Finset.univ : Finset (Fin (blockCount n d))).toList
  have hcount : 3 ≤ blockCount n d := three_le_blockCount hd hn
  have hlabels : labels ≠ [] := by
    intro hempty
    have hmember : (⟨0, by omega⟩ : Fin (blockCount n d)) ∈ labels := by
      simp [labels]
    rw [hempty] at hmember
    exact List.not_mem_nil hmember
  obtain ⟨tree, htree⟩ := exists_blockTree_leafList labels hlabels
  refine ⟨tree, ?_, ?_⟩
  · rw [htree]
    exact Finset.nodup_toList _
  · ext i
    rw [BlockTree.mem_leaves_iff, htree]
    simp [labels]
end PermanentRollout
