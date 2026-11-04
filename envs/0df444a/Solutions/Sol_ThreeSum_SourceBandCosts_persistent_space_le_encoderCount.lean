-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.persistent_space_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:44:15.695627+00:00
-- url     : https://prove2.me/submissions/eddbfbda-8192-4259-81b1-a10f6361a255

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_input_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_modulus_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_le_encoderCount
import Theorems.Thm_ThreeSum_SourceBandCosts_size_le_bandCount
import Theorems.Thm_ThreeSum_BandScales_bandSize_pos
import Theorems.Thm_ThreeSum_SourceBandLayout_work_bound


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution {base N n : ℕ} (hN : N ≤ n) :
    SourceBandLayout.work base N (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+14*encoderCount n := by
  have hs := SourceBandLayout.work_bound base N (bandSize n)
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) (bandSize_pos n)
  have hn := hN.trans (input_le_encoderCount n)
  have hb := size_le_bandCount hN
  have hm := (Nat.mul_le_mul_right
    (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) hb).trans
      (bands_modulus_le_encoderCount n)
  have hbc := hb.trans (bands_le_encoderCount n)
  nlinarith
end ThreeSum.SourceBandCosts
