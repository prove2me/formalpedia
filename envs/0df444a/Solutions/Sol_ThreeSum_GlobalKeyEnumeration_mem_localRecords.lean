-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.mem_localRecords
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:23:35.775397+00:00
-- url     : https://prove2.me/submissions/47034f87-11d6-4ab1-819f-d6c7b6fe9a36

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_mem_layers

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) (b : OutputBlock h) : b ∈ localRecords h := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,mem_layers h b.2⟩
end ThreeSum.GlobalKeyEnumeration
