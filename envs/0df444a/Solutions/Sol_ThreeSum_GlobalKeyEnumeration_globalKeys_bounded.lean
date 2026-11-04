-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.globalKeys_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:32.871351+00:00
-- url     : https://prove2.me/submissions/d5182a3f-c1bf-4171-bb7e-ba9894491d3b

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Theorems.Thm_ThreeSum_GlobalKeyEnumeration_localKeys_bounded
import Definitions.Def_WeightedCache3SUM_Alias_f8621e0ea40777d9


set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h J : ℕ) :
    ∀ x ∈ globalKeys h J,
      |x| ≤ (((512*h*localPrime h)*(localPrime h+1)^J : ℕ) : ℤ) :=
  values_bounded _ _ _ (localKeys_bounded h) J
end ThreeSum.GlobalKeyEnumeration
