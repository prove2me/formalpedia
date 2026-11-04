-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.input_le_encoderCount
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:38:18.24988+00:00
-- url     : https://prove2.me/submissions/a847ac8d-886e-4f1c-aebd-49f3989b83df

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_bandSize_le_fullOutputs
import Theorems.Thm_ThreeSum_SourceBandCosts_bands_outputs_le_encoderCount
import Theorems.Thm_ThreeSum_CostLedger_bandCount_mul_bounds


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) : n ≤ encoderCount n := by
  calc
    _ ≤ bandSize n*bandCount n := (bandCount_mul_bounds n).1
    _ ≤ fullOutputs n*bandCount n := Nat.mul_le_mul_right _ (bandSize_le_fullOutputs n)
    _ = bandCount n*fullOutputs n := Nat.mul_comm _ _
    _ ≤ _ := bands_outputs_le_encoderCount n
end ThreeSum.SourceBandCosts
