-- Prove2me | solution 1 for ThreeSum.GlobalKeyEnumeration.localKeys_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:31.711809+00:00
-- url     : https://prove2.me/submissions/81c91ac1-a5ab-4349-98d8-060037ff169f

import Definitions.Def_Submission_ThreeSum_RadixKeyLists
import Definitions.Def_Submission_ThreeSum_LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Definitions.Def_Submission_ThreeSum_GlobalKeyEnumeration
import Definitions.Def_WeightedCache3SUM_Alias_aea1baee7c22e98a

set_option autoImplicit false
open ThreeSum ThreeSum.GlobalKeyEnumeration
open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators
set_option maxHeartbeats 1800000
namespace ThreeSum.GlobalKeyEnumeration
theorem _root_.solution (h : ℕ) :
    ∀ x ∈ localKeys h, |x| ≤ ((512*h*localPrime h : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact rawOutput_abs_le _ _
end ThreeSum.GlobalKeyEnumeration
