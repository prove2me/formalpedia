-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteAEquiv_label
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:31.281978+00:00
-- url     : https://prove2.me/submissions/73dd04e0-82a9-464d-9e03-94dcc8318185

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Theorems.Thm_ThreeSum_BandRawA_items_getD


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    labelAt n g rs (finiteAEquiv n g rs s hs j).val.val=
      ⟨s,BandPartition.start g (rs.getD s default).a+j.val⟩ :=
  items_getD hs j.isLt
end ThreeSum.BandRawA
