-- Prove2me | solution 1 for ThreeSum.LightTernaryLookup.code_partition
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:12:21.90517+00:00
-- url     : https://prove2.me/submissions/8d986a74-1c76-495a-84c8-b819e808b707

import Definitions.Def_Submission_ThreeSum_LightBandLookup
import Definitions.Def_Submission_ThreeSum_LightTernaryCell
import Definitions.Def_Submission_ThreeSum_LightTernaryLookup

set_option autoImplicit false
open ThreeSum ThreeSum.LightTernaryLookup
open Light ThreeSum.LightSubsetAddress
namespace ThreeSum.LightTernaryLookup
theorem _root_.solution {n j : ℕ} (f : ℕ → ℤ) (hj : j < n)
    (hsorted : ∀ i k, i < k → k < n → f i < f k) :
    ThreeSum.BinarySearch.Partition f (f j) n (j + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    by_cases hij : i = j
    · subst i
      rfl
    · exact (hsorted i j (by omega) hj).le
  · intro i hi hin
    exact hsorted j i (by omega) hin
end ThreeSum.LightTernaryLookup
