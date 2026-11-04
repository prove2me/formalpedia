-- Prove2me | solution 1 for ThreeSum.SourceBandPairCosts.modulus_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:35:00.517547+00:00
-- url     : https://prove2.me/submissions/8995b149-df3a-4243-b28b-3a9bc17d925e

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_ThreeSum_SourceBandPairCosts_tableCount_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_modulus_le_tableCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
namespace ThreeSum.SourceBandPairCosts
theorem _root_.solution {n : ℕ} (hn : 0 < n) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n :=
  (SourceBandCosts.modulus_le_tableCount n).trans (tableCount_le_encoderCount hn)
end ThreeSum.SourceBandPairCosts
