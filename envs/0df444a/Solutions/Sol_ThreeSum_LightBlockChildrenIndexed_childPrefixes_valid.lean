-- Prove2me | solution 1 for ThreeSum.LightBlockChildrenIndexed.childPrefixes_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:42:56.014951+00:00
-- url     : https://prove2.me/submissions/2340c8bb-fa1d-47d9-8858-46cfd65175c0

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_Light_Ends_next
import Theorems.Thm_ThreeSum_ReportingHostMasks_localChild_validPrefix


set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}
namespace ThreeSum.LightBlockChildrenIndexed
theorem _root_.solution {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (next : List (Finset (Fin (512*h)))) (hn : next ∈ childPrefixes q pre hk) :
    ValidPrefix q (k+1) next := by
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hn
  exact localChild_validPrefix q pre hp hk S hS
end ThreeSum.LightBlockChildrenIndexed
