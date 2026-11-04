-- Prove2me | solution 1 for ThreeSum.BlockEncoding.row_rightSubset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:27:39.751912+00:00
-- url     : https://prove2.me/submissions/b0833e97-d66d-4bf9-b7c3-51c67c9d1238

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
    row (rightSubset t) i = (edge (t i)).val.2 := row_flat _ _
end ThreeSum.BlockEncoding
