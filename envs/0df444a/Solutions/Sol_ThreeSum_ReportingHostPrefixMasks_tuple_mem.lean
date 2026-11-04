-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixMasks.tuple_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:05:32.566225+00:00
-- url     : https://prove2.me/submissions/4a60fa8f-31fc-4a34-8a21-87c699560896

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_length
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_pairs_mem


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}
namespace ThreeSum.ReportingHostPrefixMasks
theorem _root_.solution {h k : ℕ} (p : Prefix h k) :
    tuple p ∈ RadixKeyLists.tuples (pairs (512*h) h) k := by
  apply (RadixKeyLists.mem_tuples _ _ _).mpr
  refine ⟨tuple_length p,?_⟩
  intro q hq
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
  exact (pairs_mem _).mpr (p i).property
end ThreeSum.ReportingHostPrefixMasks
