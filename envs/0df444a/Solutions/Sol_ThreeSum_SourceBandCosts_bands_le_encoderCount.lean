-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.bands_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:37:41.775607+00:00
-- url     : https://prove2.me/submissions/905e537b-9973-474b-8eb9-e302cb644a70

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_modulus_le_encoderCount
import Theorems.Thm_ThreeSum_BlockSourceEncoding_modulus_pos


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) : bandCount n ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) :=
      Nat.le_mul_of_pos_right _ (BlockSourceEncoding.modulus_pos _ _)
    _ ≤ _ := bands_modulus_le_encoderCount n
end ThreeSum.SourceBandCosts
