-- Prove2me | solution 1 for ThreeSum.SourceFiniteInputs.cover_ends
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:18:43.066004+00:00
-- url     : https://prove2.me/submissions/00ca2c68-73c2-46e9-9061-0b198fbfd116

import Definitions.Def_Submission_ThreeSum_LightGuardedWanted
import Definitions.Def_Submission_ThreeSum_LightBandRawAColor
import Definitions.Def_Submission_ThreeSum_SourceBandFinite
import Definitions.Def_Submission_ThreeSum_SourceFiniteInputs
import Theorems.Thm_ThreeSum_LightCoverKeyData_afterCover_le_keyEnd
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_table_ends_le


set_option autoImplicit false
open ThreeSum ThreeSum.SourceFiniteInputs
open Light GlobalEncoding LocalCoverBounds LightLocalCoverLayout LightLocalCoverSchedule
namespace ThreeSum.SourceFiniteInputs
theorem _root_.solution (free h J : ℕ) :
    maps free h+2*(512*h)*scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    candidates free h+scheduleSize h ≤ LightCoverKeyData.keyEnd free h J ∧
    leftCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J ∧
    rightCounts free h+rows h*localPrime h ≤ LightCoverKeyData.keyEnd free h J := by
  have hh := LightCoverKeyData.afterCover_le_keyEnd free h J
  obtain ⟨_,hl,hr,_,hc⟩ := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base free) h
  have hm : maps free h+2*(512*h)*scheduleSize h=LightCoverKeys.afterCover free h := by
    unfold maps LightCoverKeys.afterCover LightLocalCoverMetadata.nextFree
    rw [Nat.mul_comm (2*(512*h)) (scheduleSize h)]
  exact ⟨hm.le.trans hh,hc.trans hh,hl.trans hh,hr.trans hh⟩
end ThreeSum.SourceFiniteInputs
