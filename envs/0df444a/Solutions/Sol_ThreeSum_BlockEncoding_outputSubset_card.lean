-- Prove2me | solution 1 for ThreeSum.BlockEncoding.outputSubset_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:26:44.328979+00:00
-- url     : https://prove2.me/submissions/a3e28175-dfac-41c5-a14b-59e7db1f8d4f

import Definitions.Def_Submission_ThreeSum_BlockRows
import Definitions.Def_Submission_ThreeSum_RawPrefixCounts
import Definitions.Def_Submission_ThreeSum_BlockEncoding
import Theorems.Thm_ThreeSum_BlockRows_flat_card_of_balance
import Theorems.Thm_ThreeSum_LayerCounts_mem_vertices
attribute [local simp] ThreeSum.LayerCounts.mem_vertices



set_option autoImplicit false
open ThreeSum ThreeSum.BlockEncoding
set_option maxRecDepth 8000
open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows
namespace ThreeSum.BlockEncoding
theorem _root_.solution {h J : ℕ} (q : GlobalOutput h J) :
    (outputSubset q).card = J * (2 * h) :=
  flat_card_of_balance _ (fun i => LayerCounts.mem_vertices.mp (q i).2.property)
end ThreeSum.BlockEncoding
