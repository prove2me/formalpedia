-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRetention.indices_of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:34:10.05335+00:00
-- url     : https://prove2.me/submissions/6662253a-6d3d-4d6a-b405-a17b482f9940

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_table_ends_le

set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
namespace ThreeSum.LightLocalCoverRetention
theorem _root_.solution {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : Occurrence h, μ (candidates base h+s.val) = (candidateAt h s : ℤ))
    (K : Kept μ ν (nextFree base h)) :
    ∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ) := by
  intro s
  have he := (table_ends_le base h).2.2.2.2
  rw [K _ (by have hs := s.isLt; omega)]
  exact H s
end ThreeSum.LightLocalCoverRetention
