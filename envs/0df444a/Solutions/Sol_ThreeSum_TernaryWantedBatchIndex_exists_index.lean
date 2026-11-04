-- Prove2me | solution 1 for ThreeSum.TernaryWantedBatchIndex.exists_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:07.432138+00:00
-- url     : https://prove2.me/submissions/243eabaf-0ae6-4cb6-b9b4-b558242fe504

import Definitions.Def_Submission_ThreeSum_LightTernaryWantedBatch
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchCount
import Definitions.Def_Submission_ThreeSum_TernaryWantedBatchIndex
import Theorems.Thm_Light_Seg_get


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryWantedBatchIndex
open Light TernaryWantedLittleEndian
namespace ThreeSum.TernaryWantedBatchIndex
theorem _root_.solution {xs : List Entry} {e : Entry} (he : e ∈ xs) :
    ∃ i < xs.length, get xs i = e := by
  obtain ⟨i,hi,hh⟩ := List.mem_iff_getElem.mp he
  exact ⟨i,hi,by rw [get,List.getD_eq_getElem _ _ hi]; exact hh⟩
end ThreeSum.TernaryWantedBatchIndex
