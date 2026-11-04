-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteAEquiv_index
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:30.015403+00:00
-- url     : https://prove2.me/submissions/2fef9513-25b3-4743-b8a8-2f78a240c24f

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices

set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    (finiteAEquiv n g rs s hs j).val.val=count n g rs s+j.val := rfl
end ThreeSum.BandRawA
