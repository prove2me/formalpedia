-- Prove2me | solution 1 for ThreeSum.BandRawA.index_lt_firstRows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:43:54.451688+00:00
-- url     : https://prove2.me/submissions/ebe8dc55-d4f6-4300-9200-6efb91525c03

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_count_mono
import Theorems.Thm_ThreeSum_BandRawA_count_succ
import Theorems.Thm_ThreeSum_LightBandEnumeration_count_mono


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    count n g rs s+j < (firstRows n g rs i).length := by
  have hm := count_mono n g rs (show s+1 ≤ i by omega)
  rw [count_succ] at hm
  change count n g rs s+j < count n g rs i
  omega
end ThreeSum.BandRawA
