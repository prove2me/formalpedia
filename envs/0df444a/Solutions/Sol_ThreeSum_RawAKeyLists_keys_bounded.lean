-- Prove2me | solution 1 for ThreeSum.RawAKeyLists.keys_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:51.38338+00:00
-- url     : https://prove2.me/submissions/47beb773-4666-4e0c-b01f-ab3b97a2bf18

import Definitions.Def_Submission_ThreeSum_GlobalKeyOffset
import Definitions.Def_Submission_ThreeSum_LocalKeyArraySemantics
import Definitions.Def_Submission_ThreeSum_RawAKeyLists
import Theorems.Thm_ThreeSum_RawAKeyLists_key_bounded

set_option autoImplicit false
open ThreeSum ThreeSum.RawAKeyLists
open GlobalEncoding RawIncidences GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open scoped BigOperators
set_option maxHeartbeats 900000
namespace ThreeSum.RawAKeyLists
theorem _root_.solution {P : ℤ} (hP : 0 < P) (xs : List ℤ) :
    ∀ x ∈ keys P xs, |x| ≤ 2*P := by
  intro x hx
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
  exact key_bounded hP xs r
end ThreeSum.RawAKeyLists
