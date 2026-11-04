-- Prove2me | solution 1 for ThreeSum.BandRawA.valueAt_owner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:32:05.163953+00:00
-- url     : https://prove2.me/submissions/8fd8ab9c-afe0-417f-8186-4ea035a77176

import Definitions.Def_Submission_ThreeSum_BandRawAProduct
import Definitions.Def_Submission_ThreeSum_BandRawAScore
import Theorems.Thm_ThreeSum_BandRawA_values_getD_owner


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
open scoped BigOperators
set_option maxHeartbeats 1900000
set_option maxRecDepth 8000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s j : ℕ} {rs : List Record} (A : ℕ → ℤ)
    (hs : s < rs.length) (hj : j < (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (count n g rs s+j)=A (BandPartition.start g (rs.getD s default).a+j) :=
  values_getD_owner A hs hj
end ThreeSum.BandRawA
