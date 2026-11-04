-- Prove2me | solution 1 for ThreeSum.SourceBandCosts.scheduleCount_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:23.469503+00:00
-- url     : https://prove2.me/submissions/d8d02339-2c1d-43bf-9f82-3c3394975a09

import Definitions.Def_Submission_ThreeSum_LightSourceBandSetup
import Definitions.Def_Submission_ThreeSum_BlockSourceCatalogCosts
import Mathlib.Data.Nat.Choose.Vandermonde
import Definitions.Def_Submission_ThreeSum_SourceBandCosts
import Theorems.Thm_ThreeSum_TrimScales_localLength_pos


set_option autoImplicit false
open ThreeSum ThreeSum.SourceBandCosts
open Scales TrimScales StageBounds CostLedger BandScales LocalCoverBounds
namespace ThreeSum.SourceBandCosts
theorem _root_.solution (n : ℕ) : 0 < scheduleCount n := by
  unfold scheduleCount replicatedHalf
  exact pow_pos (localLength_pos _) _
end ThreeSum.SourceBandCosts
