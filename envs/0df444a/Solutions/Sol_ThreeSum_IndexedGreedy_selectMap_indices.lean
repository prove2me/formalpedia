-- Prove2me | solution 1 for ThreeSum.IndexedGreedy.selectMap_indices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:54:05.629897+00:00
-- url     : https://prove2.me/submissions/d22ce678-c0fa-4695-b120-db69036a5f99

import Definitions.Def_Submission_ThreeSum_Greedy
import Definitions.Def_Submission_ThreeSum_LightMinimum
import Definitions.Def_Submission_ThreeSum_IndexedGreedy
import Definitions.Def_WeightedCache3SUM_Alias_016e82cb2808b14f

set_option autoImplicit false
open ThreeSum ThreeSum.IndexedGreedy
open LightMinimum
namespace ThreeSum.IndexedGreedy
theorem _root_.solution {U : Type*} [DecidableEq U]
    (covers : ℕ → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap (List.range n) covers targets =
      least (fun i => -((targets.filter (covers i)).card : ℤ)) n := by
  unfold Cover.selectMap
  rw [argmax_range _ hn]
  rfl
end ThreeSum.IndexedGreedy
