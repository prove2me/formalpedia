-- Prove2me | solution 1 for ThreeSum.ReportingHostPairEnumeration.pairs_nodup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:50:47.091782+00:00
-- url     : https://prove2.me/submissions/2b66f7c1-0e59-4bda-8ea9-789ccb900f35

import Definitions.Def_Submission_ThreeSum_ReportingHostPrefixCatalog
import Definitions.Def_Submission_ThreeSum_QueryCoordinates
import Definitions.Def_Submission_ThreeSum_ReportingHostPairEnumeration
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_nodup
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_nodup

set_option autoImplicit false
open ThreeSum ThreeSum.ReportingHostPairEnumeration
open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph
set_option linter.unusedSimpArgs false
namespace ThreeSum.ReportingHostPairEnumeration
theorem _root_.solution (L h : ℕ) : (pairs L h).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro S _
    exact (rights_nodup S h).map (fun a b he => congrArg Prod.snd he)
  · exact (lefts_nodup L h).imp fun {S T} hST p hp hq => by
      obtain ⟨R,_,rfl⟩ := List.mem_map.mp hp
      obtain ⟨U,_,he⟩ := List.mem_map.mp hq
      exact hST (congrArg Prod.fst he).symm
end ThreeSum.ReportingHostPairEnumeration
