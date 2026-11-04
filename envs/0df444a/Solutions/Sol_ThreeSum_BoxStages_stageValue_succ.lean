-- Prove2me | solution 1 for ThreeSum.BoxStages.stageValue_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:44:59.352089+00:00
-- url     : https://prove2.me/submissions/6f4bbfb2-6cc8-467d-a8a8-779d758475ce

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_BoxStages_nextCoord_not_mem
import Theorems.Thm_ThreeSum_BoxStages_prefix_succ
import Theorems.Thm_ThreeSum_SubsetStages_nextCoord_not_mem
import Definitions.Def_WeightedCache3SUM_Alias_790a7eeb73d26fe5


set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset
namespace ThreeSum.BoxStages
theorem _root_.solution {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,prefix_succ hj]
  exact Subset.partialZeta_insert f S (initialCoords L j) (nextCoord j hj) (nextCoord_not_mem hj)
end ThreeSum.BoxStages
