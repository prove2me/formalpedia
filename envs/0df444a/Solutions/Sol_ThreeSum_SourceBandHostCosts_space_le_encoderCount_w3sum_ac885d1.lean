-- Prove2me | solution 1 for ThreeSum.SourceBandHostCosts.space_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:16:20.08943+00:00
-- url     : https://prove2.me/submissions/c44a958b-a4fa-4657-84d0-79d5348a86a7

import Definitions.Def_Submission_ThreeSum_LightSourceBandHostProgram
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Definitions.Def_Submission_ThreeSum_SourceBandHostCosts
import Theorems.Thm_ThreeSum_SourceBandHostCosts_bankHeader_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_space_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandPairCosts_next_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandHostCosts
open Scales TrimScales StageBounds CostLedger BandScales
namespace ThreeSum.SourceBandHostCosts
theorem _root_.solution {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+16 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.space_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hn hNL hNR
  unfold LightSourceBandHost.space
  apply max_le
  · unfold LightSourceBandPair.space LightSourceResidues.space
    nlinarith
  · have hm : 0 ≤ max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2) := Nat.zero_le _
    nlinarith only [hh,hb,hm]
end ThreeSum.SourceBandHostCosts
