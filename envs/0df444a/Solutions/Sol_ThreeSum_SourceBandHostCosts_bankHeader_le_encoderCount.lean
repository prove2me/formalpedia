-- Prove2me | solution 1 for ThreeSum.SourceBandHostCosts.bankHeader_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:57:25.08642+00:00
-- url     : https://prove2.me/submissions/1c4efbee-723e-4e1e-8439-a721b0e8576d

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_SourceBandHostCosts_occurrenceRows_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandPairCosts_next_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceBandHostCosts
theorem _root_.solution {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      base+(29+blockCount (inputBits n))*encoderCount n+9 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hr := occurrenceRows_le_encoderCount hn
  unfold LightSourceBandHost.bankHeader LightSourceBandHost.occurrenceBase
  nlinarith
end ThreeSum.SourceBandHostCosts
