-- Prove2me | solution 1 for ThreeSum.SourceBandPairCosts.next_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:17:30.738725+00:00
-- url     : https://prove2.me/submissions/9f06eb80-d381-4d58-baa9-bcd4cb035139

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_SourceBandLayout_work_bound


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
namespace ThreeSum.SourceBandPairCosts
theorem _root_.solution (base NL NR g m : ℕ) (hg : 0 < g) :
    next base NL NR g m ≤ base+4*(NL+NR)+
      (BandPartition.size NL g+BandPartition.size NR g)*(3*m+7)+m+9 := by
  have hl := SourceBandLayout.work_bound (leftBase base) NL g m hg
  have hr := SourceBandLayout.work_bound (rightBase base NL g m) NR g m hg
  change rightBase base NL g m ≤ _ at hl
  change zeroBase base NL NR g m ≤ _ at hr
  unfold next leftBase at *
  nlinarith
end ThreeSum.SourceBandPairCosts
