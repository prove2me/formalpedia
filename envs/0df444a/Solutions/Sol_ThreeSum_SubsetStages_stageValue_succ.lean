-- Prove2me | solution 1 for ThreeSum.SubsetStages.stageValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:35:49.442852+00:00
-- url     : https://prove2.me/submissions/ac1f0fed-cac8-4e4d-a0bf-0050776fdca2

import Definitions.Def_Submission_ThreeSum_Subset
import Definitions.Def_Submission_ThreeSum_SubsetAddress
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Theorems.Thm_ThreeSum_SubsetStages_nextCoord_not_mem
import Theorems.Thm_ThreeSum_SubsetStages_suffix_succ
import Definitions.Def_WeightedCache3SUM_Alias_790a7eeb73d26fe5


set_option autoImplicit false
open ThreeSum ThreeSum.SubsetStages
open Finset
namespace ThreeSum.SubsetStages
theorem _root_.solution {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,suffix_succ hj]
  exact Subset.partialZeta_insert f S (suffix L j) (nextCoord j hj) (nextCoord_not_mem hj)
end ThreeSum.SubsetStages
