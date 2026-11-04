-- Prove2me | solution 1 for ThreeSum.LightSourceGather.value_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:53:10.597837+00:00
-- url     : https://prove2.me/submissions/ad1a20f3-5ea5-467c-aefc-6847231f5481

import Definitions.Def_Submission_ThreeSum_BlockSourceEncoding
import Definitions.Def_Submission_ThreeSum_LightSourceGather
import Theorems.Thm_ThreeSum_LightResidues_residue_lt


set_option autoImplicit false
open ThreeSum ThreeSum.LightSourceGather
open Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
namespace ThreeSum.LightSourceGather
theorem _root_.solution {m B : ℕ} (hm : 0 < m) (endpoint : ℕ → ℤ) (flag hist : ℕ → ℕ)
    (hhist : ∀ r < m, hist r ≤ B) (i : ℕ) : value m endpoint flag hist i ≤ B := by
  unfold value
  split
  · exact hhist _ (LightResidues.residue_lt hm 1 _)
  · omega
end ThreeSum.LightSourceGather
