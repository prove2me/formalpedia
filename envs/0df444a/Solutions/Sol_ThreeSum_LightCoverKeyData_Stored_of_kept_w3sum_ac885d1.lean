-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.Stored.of_kept_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:04:53.272209+00:00
-- url     : https://prove2.me/submissions/27679536-be96-46ab-8f4d-1a8312e3e30b

import Definitions.Def_Submission_ThreeSum_LightCoverKeys
import Definitions.Def_Submission_ThreeSum_LightCoverKeyData
import Theorems.Thm_ThreeSum_LightCoverKeyData_global_length
import Theorems.Thm_ThreeSum_LightCoverKeyData_layer_end_le_header
import Theorems.Thm_ThreeSum_LightCoverKeyData_afterCover_le_keyEnd
import Theorems.Thm_Light_MatAt_congr
import Theorems.Thm_Light_Seg_congr
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_data_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_header_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_indices_of_kept
import Theorems.Thm_ThreeSum_LightLocalCoverRetention_rows_of_kept


set_option autoImplicit false
open ThreeSum ThreeSum.LightCoverKeyData
open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
namespace ThreeSum.LightCoverKeyData
namespace Stored
theorem _root_.solution {μ ν : ℕ → ℤ} {free h J : ℕ} (H : Stored μ free h J)
    (K : Kept μ ν (keyEnd free h J)) : Stored ν free h J := by
  have hafter := afterCover_le_keyEnd free h J
  have hafterK : Kept μ ν (LightCoverKeys.afterCover free h) := fun i hi => K i (by omega)
  refine ⟨?_,?_,LightLocalCoverRetention.header_of_kept H.header hafterK,
    LightLocalCoverRetention.data_of_kept H.data hafterK,
    LightLocalCoverRetention.rows_of_kept H.rows hafterK,
    LightLocalCoverRetention.indices_of_kept H.indices hafterK,?_⟩
  · rw [K _ (by unfold keyEnd; omega)]
    exact H.count
  · apply H.keys.congr
    intro i hi
    rw [global_length] at hi
    exact K _ (by unfold keyEnd; omega)
  · intro i hi
    have hh := layer_end_le_header free h J
    rw [K _ (by unfold keyEnd; omega)]
    exact H.masks i hi
end Stored
end ThreeSum.LightCoverKeyData
