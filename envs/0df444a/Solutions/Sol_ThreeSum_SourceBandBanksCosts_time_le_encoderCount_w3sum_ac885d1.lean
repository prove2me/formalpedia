-- Prove2me | solution 1 for ThreeSum.SourceBandBanksCosts.time_le_encoderCount_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T14:03:02.161053+00:00
-- url     : https://prove2.me/submissions/185e7b6b-acf3-472d-8073-a8c523ae29a4

import Definitions.Def_Submission_ThreeSum_LightSourceBandBanksProgram
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Definitions.Def_Submission_ThreeSum_SourceBandBanksCosts
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_count_le_bandCount
import Theorems.Thm_ThreeSum_SourceBandBanksCosts_bandCount_pos
import Definitions.Def_WeightedCache3SUM_Alias_dd622383cbc3b06f
import Theorems.Thm_ThreeSum_BlockSourceStageCosts_work_le_encoderCount
import Theorems.Thm_ThreeSum_MassScales_bandCount_pos
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandBanksCosts
open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress
namespace ThreeSum.SourceBandBanksCosts
theorem _root_.solution {NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+1300)*
        encoderCount n+1220 := by
  have hcount := count_le_bandCount hNL hNR
  have hpos := bandCount_pos hn
  have hrows := Nat.le_mul_of_pos_left
    (LightSourceOccurrenceArray.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (blockCount (inputBits n))) hpos
  have hbatch := Nat.mul_le_mul_right
    (LightBlockSourceBatch.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)) hcount
  have ht : LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      BlockSourceCatalogCosts.work n+1300*bandCount n+1220 := by
    unfold LightSourceBandBanks.time LightSourceBandBankBatch.time LightSourceBandBankStep.time
      BlockSourceCatalogCosts.work LightBlockSourceCatalog.time
    nlinarith
  have hw := BlockSourceCatalogCosts.work_le_encoderCount n
  have hb := SourceBandCosts.bands_le_encoderCount n
  nlinarith
end ThreeSum.SourceBandBanksCosts
