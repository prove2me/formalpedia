-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.four_le_scheduleSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:03:33.607358+00:00
-- url     : https://prove2.me/submissions/979fc186-6772-4c50-84dd-7b640b0530da

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts

set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (h : ℕ) : 4 ≤ GlobalEncoding.scheduleSize h := by
  unfold GlobalEncoding.scheduleSize LocalHashMoments.scheduleLength
  calc
    4 ≤ 320 := by decide
    _ ≤ 320*(2*h+1) := Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
end ThreeSum.SourceBandCosts
