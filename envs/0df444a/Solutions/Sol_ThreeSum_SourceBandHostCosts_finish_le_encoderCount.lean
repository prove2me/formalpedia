-- Prove2me | solution 1 for ThreeSum.SourceBandHostCosts.finish_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:06:30.926209+00:00
-- url     : https://prove2.me/submissions/c4e95ec8-9b89-4faf-8c77-4213fe73b5a4

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_SourceBandHostCosts_bankHeader_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_finish_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceBandHostCosts
theorem _root_.solution {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+14 := by
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.finish_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hNL hNR
  unfold LightSourceBandHost.finish
  nlinarith
end ThreeSum.SourceBandHostCosts
