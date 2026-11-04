-- Prove2me | solution 1 for ThreeSum.SourceControlCosts.finish_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:48:19.118421+00:00
-- url     : https://prove2.me/submissions/e6ea3855-798d-4965-8e1b-26a2f46ee63a

import Definitions.Def_Submission_ThreeSum_LightSourceControlsHostProgram
import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandHostCosts_finish_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceControlCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceControlCosts
theorem _root_.solution {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 := by
  have hs := SourceBandHostCosts.finish_le_encoderCount (base := base+3) hn hNL hNR
  unfold LightSourceControlsHost.finish LightSourceControlsHost.sourceBase
  omega
end ThreeSum.SourceControlCosts
