-- Prove2me | solution 1 for ThreeSum.BlockEncoding.row_outputSubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:40.977961+00:00
-- url     : https://prove2.me/submissions/fb24c035-a819-4e3f-961c-8c4861f40bb2

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Theorems.Thm_ThreeSum_BlockRows_row_flat
attribute [local simp] ThreeSum.BlockRows.row_flat



set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
namespace ThreeSum.BlockEncoding
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) (i : Fin J) :
    row (outputSubset q) i = (q i).2.val := row_flat _ _
end ThreeSum.BlockEncoding
