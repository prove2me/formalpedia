-- Prove2me | solution 1 for ThreeSum.MaskUnion.scanSet_succ_already
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:14.698986+00:00
-- url     : https://prove2.me/submissions/48bb56a5-c134-4287-a90a-92a1d56b58d7

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
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∈ A) :
    scanSet A B (j+1) = scanSet A B j := by
  rw [scanSet_succ_mem A B hj hb]
  exact Finset.insert_eq_of_mem ((current_mem_iff A B hj).mpr ha)
end ThreeSum.MaskUnion
