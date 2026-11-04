-- Prove2me | solution 1 for ThreeSum.BoxStages.stageValue_eq_boxSum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:18:14.184784+00:00
-- url     : https://prove2.me/submissions/b38050b1-56af-41d6-bd45-9d76d59403e6

import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_SparseBoxes
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_WeightedCache3SUM_Alias_027772657a72dd80

set_option autoImplicit false
open ThreeSum ThreeSum.BoxStages
open Finset
namespace ThreeSum.BoxStages
theorem _root_.solution {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (j : ℕ) (flags : Finset (Fin L)) :
    stageValue weight j flags = SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight :=
  partialZeta_eq_boxSum weight flags (initialCoords L j)
end ThreeSum.BoxStages
