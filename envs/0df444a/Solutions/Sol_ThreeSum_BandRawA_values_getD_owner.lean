-- Prove2me | solution 1 for ThreeSum.BandRawA.values_getD_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:23:35.95523+00:00
-- url     : https://prove2.me/submissions/ca7283e1-7147-4391-b666-3343c3a18e59

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_index_lt_items
import Theorems.Thm_ThreeSum_BandRawA_items_getD
import Theorems.Thm_ThreeSum_BandRawA_values_getD

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s j : ℕ} {rs : List Record} (f : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    (values f (items n g rs)).getD (count n g rs s+j) 0=
      f (BandPartition.start g (rs.getD s default).a+j) := by
  rw [values_getD f (index_lt_items hs hj),items_getD hs hj]
end ThreeSum.BandRawA
