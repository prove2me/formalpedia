-- Prove2me | solution 1 for ThreeSum.BoxStages.query_box_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:21:16.3839+00:00
-- url     : https://prove2.me/submissions/9b39b888-b656-4827-94f9-a27cfa736231

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Theorems.Thm_ThreeSum_BoxStages_stageValue_eq_boxSum
import Theorems.Thm_ThreeSum_BoxStages_queryFree_prefix

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset
namespace ThreeSum.BoxStages
theorem _root_.solution {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight =
      stageValue weight (u.min' hu).val (q \ u) := by
  rw [queryFree_prefix q u hu,stageValue_eq_boxSum]
end ThreeSum.BoxStages
