-- Prove2me | solution 1 for ThreeSum.SourceControlLayout.span_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:40:41.982612+00:00
-- url     : https://prove2.me/submissions/edcc6bee-6de0-4cc8-857f-b878f981668c

import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceControlLayout
import Theorems.Thm_ThreeSum_SourceControlLayout_scratch_eq
import Theorems.Thm_ThreeSum_SourceControlLayout_stride_eq
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_span_eq


set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlLayout
open GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress
namespace ThreeSum.SourceControlLayout
theorem _root_.solution (h J cut : ℕ) :
    span J (J*(512*h)) (downsetCap (J*(512*h)) cut) (LightBlockSourceCatalog.count h J)
      (Nat.log 2 ((512*h)*localPrime h+1)) (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)) =
      SourceBandBankLayout.span h J cut := by
  unfold span
  rw [scratch_eq,stride_eq,SourceBandBanksCosts.span_eq]
end ThreeSum.SourceControlLayout
