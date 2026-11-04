-- Prove2me | solution 1 for ThreeSum.SourceFiniteCosts.finish_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:58:10.67427+00:00
-- url     : https://prove2.me/submissions/384a6d27-e5ce-4301-9e2f-e9b61ccd59fd

import Definitions.Def_Submission_ThreeSum_SourceControlCosts
import Definitions.Def_Submission_ThreeSum_SourceFiniteCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandHostCosts_finish_le_encoderCount
import Theorems.Thm_ThreeSum_SourceControlCosts_finish_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceFiniteCosts
theorem _root_.solution {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ finish base n :=
  SourceControlCosts.finish_le_encoderCount hn hNL hNR
end ThreeSum.SourceFiniteCosts
