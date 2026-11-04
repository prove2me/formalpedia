-- Prove2me | solution 1 for ThreeSum.ReportingHostPrefixMasks.tuple_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:10:09.220303+00:00
-- url     : https://prove2.me/submissions/913729f1-b0f0-4c53-9101-d5f955cc5bde

import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_BlockMaskLayout
import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixMasks
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_mem
import Theorems.Thm_ThreeSum_ReportingHostPrefixMasks_tuple_ofTuple
import Theorems.Thm_ThreeSum_RadixKeyLists_mem_tuples


set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPrefixMasks
open Finset ThreeSum.SubsetAddress BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open BlockForced
open ReportingHostPrefixCatalog ReportingHostPairEnumeration
open scoped BigOperators
set_option maxHeartbeats 500000
variable {α : Type*}
namespace ThreeSum.ReportingHostPrefixMasks
theorem _root_.solution {h k : ℕ} (xs : List (Finset (Fin (512*h)) × Finset (Fin (512*h)))) :
    xs ∈ RadixKeyLists.tuples (pairs (512*h) h) k ↔ ∃ p : Prefix h k, tuple p = xs := by
  constructor
  · intro hx
    obtain ⟨hlen,hmem⟩ := (RadixKeyLists.mem_tuples _ _ _).mp hx
    exact ⟨ofTuple xs hlen hmem,tuple_ofTuple xs hlen hmem⟩
  · rintro ⟨p,rfl⟩
    exact tuple_mem p
end ThreeSum.ReportingHostPrefixMasks
