-- Prove2me | solution 1 for ThreeSum.SourceFiniteCosts.word_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:00:42.835198+00:00
-- url     : https://prove2.me/submissions/04858218-e158-4d37-957f-2382f870e2c8

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Theorems.Thm_ThreeSum_SourceBandBankLayout_word_mono


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceFiniteCosts
theorem _root_.solution {NL NR NL' NR' g p h J cut U D : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightSourceControlsHost.word NL NR g p h J cut U D ≤
      LightSourceControlsHost.word NL' NR' g p h J cut U D := by
  have hs := SourceBandBankLayout.word_mono (h := h) (J := J) hl hr
  unfold LightSourceControlsHost.word LightSourceBandHost.word LightSourceBandPair.word
    LightSourceBandStep.word LightSourceBandBanks.word LightSourceBandBankStep.word
  omega
end ThreeSum.SourceFiniteCosts
