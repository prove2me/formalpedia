-- Prove2me | solution 1 for ThreeSum.BandRawA.finiteAEquiv_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:54:32.502668+00:00
-- url     : https://prove2.me/submissions/27878f4e-e88a-40da-8586-367845d2df76

import Definitions.Def_Submission_ThreeSum_BandRawAFinite
import Definitions.Def_Submission_ThreeSum_BandRawAFiniteSlices
import Theorems.Thm_ThreeSum_BandRawA_valueAt_owner


set_option autoImplicit false
open ThreeSum ThreeSum.BandRawA
open BandCandidateRows Finset
set_option maxHeartbeats 1500000
set_option maxRecDepth 7000
namespace ThreeSum.BandRawA
theorem _root_.solution (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (A : ℕ → ℤ) (j : Fin (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (finiteAEquiv n g rs s hs j).val.val=
      A (BandPartition.start g (rs.getD s default).a+j.val) :=
  valueAt_owner A hs j.isLt
end ThreeSum.BandRawA
