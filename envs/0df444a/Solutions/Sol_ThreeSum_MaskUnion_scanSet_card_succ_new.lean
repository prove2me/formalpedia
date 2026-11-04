-- Prove2me | solution 1 for ThreeSum.MaskUnion.scanSet_card_succ_new
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:16.106738+00:00
-- url     : https://prove2.me/submissions/afba9b41-4442-45da-a15e-8081bb2b0749

import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_MaskUnion
import Theorems.Thm_ThreeSum_MaskUnion_scanSet_succ_mem
import Theorems.Thm_ThreeSum_MaskUnion_current_mem_iff

set_option autoImplicit false
open ThreeSum ThreeSum.MaskUnion
open Finset ThreeSum.SubsetAddress
namespace ThreeSum.MaskUnion
theorem _root_.solution {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∉ A) :
    (scanSet A B (j+1)).card = (scanSet A B j).card+1 := by
  rw [scanSet_succ_mem A B hj hb,Finset.card_insert_of_notMem]
  exact fun h => ha ((current_mem_iff A B hj).mp h)
end ThreeSum.MaskUnion
