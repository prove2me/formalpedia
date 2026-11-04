-- Prove2me | solution 1 for ThreeSum.LightBlockChildrenIndexed.childAt_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:47:03.76579+00:00
-- url     : https://prove2.me/submissions/a2680554-d943-4645-bee9-f3327e33809b

import Definitions.Def_Submission_ThreeSum_LightBlockChildren
import Definitions.Def_Submission_ThreeSum_LightBlockQuery
import Definitions.Def_Submission_ThreeSum_LightBlockChildrenIndexed
import Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childPrefixes_valid
import Theorems.Thm_ThreeSum_LightBlockChildrenIndexed_childAt_eq_get

set_option autoImplicit false
open ThreeSum ThreeSum.LightBlockChildrenIndexed
open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds
variable {lim : Limits}
namespace ThreeSum.LightBlockChildrenIndexed
theorem _root_.solution {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (i : ℕ) (hi : i < groupSize h) : ValidPrefix q (k+1) (childAt q pre hk i) := by
  rw [childAt_eq_get q pre hk i hi]
  exact childPrefixes_valid q pre hp hk _ (List.getElem_mem _)
end ThreeSum.LightBlockChildrenIndexed
