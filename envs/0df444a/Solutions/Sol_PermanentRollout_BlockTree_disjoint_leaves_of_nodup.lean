-- Prove2me | solution 1 for PermanentRollout.BlockTree.disjoint_leaves_of_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:07.661825+00:00
-- url     : https://prove2.me/submissions/d140b2e4-e8bc-49eb-ba93-5c429f111f75

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open scoped BigOperators
open PermanentRollout.BlockTree
namespace PermanentRollout.BlockTree
theorem _root_.solution {ι : Type*} [DecidableEq ι]
    {left right : BlockTree ι}
    (h : (BlockTree.branch left right).leafList.Nodup) :
    Disjoint left.leaves right.leaves := by
  rw [Finset.disjoint_left]
  intro i hi_left hi_right
  have hparts := (List.nodup_append.mp h).2.2
  exact hparts i ((mem_leaves_iff left i).mp hi_left)
    i ((mem_leaves_iff right i).mp hi_right) rfl
end PermanentRollout.BlockTree
