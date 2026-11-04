-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.bandSize_le_fullOutputs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:33:15.234832+00:00
-- url     : https://prove2.me/submissions/3ec49d52-dd27-4092-b2ca-e86e0eb0b203

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_SourceBandCosts_typedOutputs_le_fullOutputs
import Theorems.Thm_ThreeSum_BandScales_bandDivisor_pos
import Theorems.Thm_ThreeSum_BandScales_typedOutputs_pos


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) : bandSize n ≤ fullOutputs n := by
  have hb : bandSize n ≤ bandRoot n := by
    apply (ceilDiv_le_iff_le_mul (a := bandDivisor n) (bandDivisor_pos n)).mpr
    exact Nat.le_mul_of_pos_left _ (bandDivisor_pos n)
  have hr : bandRoot n ≤ typedOutputs n := by
    have hs := Nat.sqrt_le_self (typedOutputs n-1)
    have hp := typedOutputs_pos n
    unfold bandRoot rootCeiling
    omega
  exact hb.trans (hr.trans (typedOutputs_le_fullOutputs n))
end ThreeSum.SourceBandCosts
