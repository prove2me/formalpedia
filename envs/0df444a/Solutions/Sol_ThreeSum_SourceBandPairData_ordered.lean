-- Prove2me | solution 1 for ThreeSum.SourceBandPairData.ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:05:43.388026+00:00
-- url     : https://prove2.me/submissions/7f8490b0-3dbc-499b-aa06-41d232a21684

import Definitions.Def_Submission_ThreeSum_SourceBandData
import Definitions.Def_Submission_ThreeSum_SourceBandPairData
import Theorems.Thm_ThreeSum_SourceBandPairData_work_ge
import Theorems.Thm_Light_Ends_next


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairData
open Light BandPartition
namespace ThreeSum.SourceBandPairData
theorem _root_.solution (base NL NR g m : ℕ) :
    leftBase base ≤ rightBase base NL g m ∧
    rightBase base NL g m ≤ zeroBase base NL NR g m ∧
    zeroBase base NL NR g m < next base NL NR g m := by
  exact ⟨work_ge _ _ _ _,work_ge _ _ _ _,by unfold next; omega⟩
end ThreeSum.SourceBandPairData
