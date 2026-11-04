-- Prove2me | solution 1 for ThreeSum.LightLocalCoverRetention.data_of_kept
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:49.532811+00:00
-- url     : https://prove2.me/submissions/b7a1d668-5bd7-46a9-8396-6ac36fccfd19

import Definitions.Def_Submission_ThreeSum_LightLocalCoverInit
import Definitions.Def_Submission_ThreeSum_LightLocalCoverRetention
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_table_ends_le
import Definitions.Def_WeightedCache3SUM_Alias_82db098e10427a83


set_option autoImplicit false
open ThreeSum ThreeSum.LightLocalCoverRetention
open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata
set_option maxHeartbeats 1000000
namespace ThreeSum.LightLocalCoverRetention
theorem _root_.solution {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : Data μ h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h))
    (K : Kept μ ν (nextFree base h)) :
    Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) := by
  obtain ⟨hm,hl,hr,hx,_⟩ := table_ends_le base h
  exact H.of_kept K hm hl hr hx
end ThreeSum.LightLocalCoverRetention
