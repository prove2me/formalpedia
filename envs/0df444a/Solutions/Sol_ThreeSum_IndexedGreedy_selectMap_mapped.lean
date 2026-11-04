-- Prove2me | solution 1 for ThreeSum.IndexedGreedy.selectMap_mapped
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:51:34.093617+00:00
-- url     : https://prove2.me/submissions/8a10a499-426f-47c2-ae3b-8ebbc9233160

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_WeightedCache3SUM_Alias_016e82cb2808b14f
import Theorems.Thm_ThreeSum_IndexedGreedy_argmax_map

set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum
namespace ThreeSum.IndexedGreedy
theorem _root_.solution {α : Type*} [Inhabited α]
    {U : Type*} [DecidableEq U]
    (g : ℕ → α) (covers : α → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap ((List.range n).map g) covers targets =
      g (least (fun i => -((targets.filter (covers (g i))).card : ℤ)) n) := by
  unfold Cover.selectMap
  rw [argmax_map,argmax_range _ hn]
  rfl
end ThreeSum.IndexedGreedy
