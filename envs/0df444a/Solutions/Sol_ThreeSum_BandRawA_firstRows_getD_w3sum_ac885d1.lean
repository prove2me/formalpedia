-- Prove2me | solution 1 for ThreeSum.BandRawA.firstRows_getD_w3sum_ac885d1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:58:40.200838+00:00
-- url     : https://prove2.me/submissions/49b1b3c5-8686-49ad-bbee-4c1373d1fff8

import Definitions.Def_Submission_ThreeSum_BandRawAMemory
import Definitions.Def_Submission_ThreeSum_BandRawAIndex
import Theorems.Thm_ThreeSum_BandRawA_index_lt_firstRows
import Theorems.Thm_ThreeSum_BandRawA_firstRows_succ
import Theorems.Thm_ThreeSum_BandRawA_row_getElem


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows
set_option maxHeartbeats 1700000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution {n g s i j : ℕ} {rs : List Record}
    (hs : s < i) (hj : j < (row n g s (rs.getD s default)).length) :
    (firstRows n g rs i).getD (count n g rs s+j) default=
      ⟨s,BandPartition.start g (rs.getD s default).a+j⟩ := by
  induction i with
  | zero => omega
  | succ i ih =>
    rw [firstRows_succ]
    by_cases hsi : s < i
    · rw [List.getD_append _ _ _ _ (index_lt_firstRows hsi hj)]
      exact ih hsi
    · have he : s=i := by omega
      subst s
      rw [List.getD_append_right _ _ _ _ (by change count n g rs i ≤ count n g rs i+j; omega)]
      change (row n g i (rs.getD i default)).getD (count n g rs i+j-count n g rs i) default=_
      rw [Nat.add_sub_cancel_left,List.getD_eq_getElem _ _ hj,row_getElem hj]
end ThreeSum.BandRawA
