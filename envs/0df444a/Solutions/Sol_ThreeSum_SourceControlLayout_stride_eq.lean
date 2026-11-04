-- Prove2me | solution 1 for ThreeSum.SourceControlLayout.stride_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:29:06.244431+00:00
-- url     : https://prove2.me/submissions/fe7cf70f-832b-4e51-b1cb-3b4c397229e7

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceControlLayout

set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress
namespace ThreeSum.SourceControlLayout
theorem _root_.solution (W cut : ℕ) :
    stride W (downsetCap W cut)=LightBlockSourceBatchLayout.stride W cut+2 := by
  unfold stride LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
  ring
end ThreeSum.SourceControlLayout
