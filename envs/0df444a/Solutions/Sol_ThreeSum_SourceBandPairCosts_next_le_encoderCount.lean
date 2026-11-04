-- Prove2me | solution 1 for ThreeSum.SourceBandPairCosts.next_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:50:23.032199+00:00
-- url     : https://prove2.me/submissions/ec020a37-5124-44d2-902a-d35bd21db714

import Definitions.Def_Submission_ThreeSum_LightSourceBandPair
import Definitions.Def_Submission_ThreeSum_SourceBandPairCosts
import Theorems.Thm_ThreeSum_SourceBandPairCosts_modulus_le_encoderCount
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_SourceBandCosts_persistent_space_le_encoderCount


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandPairCosts
open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData
namespace ThreeSum.SourceBandPairCosts
theorem _root_.solution {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    next base NL NR (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+29*encoderCount n+9 := by
  have hl := SourceBandCosts.persistent_space_le_encoderCount (base := leftBase base) hNL
  have hr := SourceBandCosts.persistent_space_le_encoderCount
    (base := rightBase base NL (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)))) hNR
  have hm := modulus_le_encoderCount hn
  change rightBase base NL (bandSize n) _ ≤ _ at hl
  change zeroBase base NL NR (bandSize n) _ ≤ _ at hr
  unfold next leftBase at *
  omega
end ThreeSum.SourceBandPairCosts
