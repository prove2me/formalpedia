-- Prove2me | solution 1 for ThreeSum.MaskUnion.scanSet_succ_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:13.436727+00:00
-- url     : https://prove2.me/submissions/d8b9d175-4778-487d-9d8f-5d9fdc0d83aa

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
import Theorems.Thm_ThreeSum_BoxStages_prefix_succ


set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskUnion
theorem _root_.solution {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∉ B) : scanSet A B (j+1) = scanSet A B j := by
  rw [scanSet,BoxStages.prefix_succ hj]
  change A ∪ (B ∩ insert ⟨j,hj⟩ (BoxStages.initialCoords W j)) = _
  rw [Finset.inter_insert_of_notMem hb]
  rfl
end ThreeSum.MaskUnion
