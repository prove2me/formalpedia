-- Prove2me | solution 1 for ThreeSum.SourceFiniteData.source_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:59:20.662166+00:00
-- url     : https://prove2.me/submissions/f4ea05e3-7f82-47d0-aafb-d5208222980f

import Definitions.Def_Submission_ThreeSum_SourceFiniteData
import Definitions.Def_Submission_ThreeSum_EncodedColorSourceRetention
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_SourceBandPairData_ordered


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteData
open Light
namespace ThreeSum.SourceFiniteData
theorem _root_.solution (base NL NR g h J cut : ℕ) :
    base+3 ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    SourceBandPairData.next (LightSourceControlsHost.sourceBase base) NL NR g
      (BlockSourceEncoding.modulus h J) ≤ LightSourceControlsHost.finish base NL NR g h J cut ∧
    LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) NL NR g h J+5 ≤
      LightSourceControlsHost.finish base NL NR g h J cut := by
  have ho := SourceBandPairData.ordered (LightSourceControlsHost.sourceBase base)
    NL NR g (BlockSourceEncoding.modulus h J)
  unfold LightSourceControlsHost.finish LightSourceBandHost.finish SourceBandBankData.finish
    SourceBandBankLayout.baseAt SourceBandBankData.first LightSourceBandHost.bankHeader
    LightSourceBandHost.occurrenceBase LightSourceControlsHost.sourceBase
  unfold SourceBandPairData.leftBase LightSourceControlsHost.sourceBase at ho
  omega
end ThreeSum.SourceFiniteData
