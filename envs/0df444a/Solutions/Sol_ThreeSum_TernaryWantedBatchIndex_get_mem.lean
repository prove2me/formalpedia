-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchIndex.get_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:22:02.269536+00:00
-- url     : https://prove2.me/submissions/a398718c-a26a-41b4-a930-9a186da7e896

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchIndex
theorem _root_.solution {xs : List Entry} {i : ℕ} (hi : i < xs.length) : get xs i ∈ xs := by
  rw [get,List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi
end ThreeSum.TernaryWantedBatchIndex
