-- Prove2me | solution 1 for ThreeSum.BandRawA.values_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:36:33.328838+00:00
-- url     : https://prove2.me/submissions/f8e40131-bd11-492f-bdee-0f27ac640914

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_List_getD_map_of_lt


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g k : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hk : k < (items n g rs).length) :
    (values f (items n g rs)).getD k 0=f (labelAt n g rs k).position := by
  unfold values labelAt
  rw [List.getD_map_of_lt _ hk default 0]
end ThreeSum.BandRawA
