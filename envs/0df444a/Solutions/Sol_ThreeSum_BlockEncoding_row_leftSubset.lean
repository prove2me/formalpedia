-- Prove2me | solution 1 for ThreeSum.BlockEncoding.row_leftSubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:38.47906+00:00
-- url     : https://prove2.me/submissions/5ff158e3-1907-4897-bf32-d07ab5e27873

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
theorem _root_.solution {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (leftSubset t) i = (edge (t i)).val.1 := row_flat _ _
end ThreeSum.BlockEncoding
