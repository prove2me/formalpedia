-- Prove2me | solution 1 for ThreeSum.SourceBandPairCosts.time_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:41:25.578761+00:00
-- url     : https://prove2.me/submissions/d648645f-e34f-4d8d-a680-f69981f8ce21

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_ThreeSum_SourceBandPairCosts_modulus_le_encoderCount
import Definitions.Def_WeightedCache3SUM_Alias_8b3592271bea283a


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
namespace ThreeSum.SourceBandPairCosts
theorem _root_.solution {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandPair.time NL NR (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+3905)*encoderCount n+3139 := by
  have hl := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNL
  have hr := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNR
  have hm := modulus_le_encoderCount hn
  unfold LightSourceBandPair.time Light.fillTime
  nlinarith
end ThreeSum.SourceBandPairCosts
