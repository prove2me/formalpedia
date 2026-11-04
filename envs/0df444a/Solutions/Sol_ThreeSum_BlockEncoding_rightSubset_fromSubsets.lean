-- Prove2me | solution 1 for ThreeSum.BlockEncoding.rightSubset_fromSubsets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:43.335488+00:00
-- url     : https://prove2.me/submissions/918ddf96-7381-407c-aba7-8e76705ebb48

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Theorems.Thm_ThreeSum_BlockRows_flat_row
attribute [local simp] ThreeSum.BlockRows.flat_row



set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
namespace ThreeSum.BlockEncoding
theorem _root_.solution {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    rightSubset (fromSubsets o S V hS hV hd) = V := flat_row V
end ThreeSum.BlockEncoding
