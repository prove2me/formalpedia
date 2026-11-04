-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.bands_modulus_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:34:58.490141+00:00
-- url     : https://prove2.me/submissions/5c9f51bf-b30c-46aa-9b27-1de5edb2dff2

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_modulus_le_tableCount

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) :
    bandCount n*BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n := by
  calc
    _ ≤ bandCount n*tableCount n := Nat.mul_le_mul_left _ (modulus_le_tableCount n)
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring
end ThreeSum.SourceBandCosts
