-- Prove2me | solution 1 for ThreeSum.TernaryWantedDictionaryFiber.values_fiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:17:47.987285+00:00
-- url     : https://prove2.me/submissions/0fa80b53-69de-46fc-a24e-709fe5c69ebc

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_filtered_values
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers
namespace ThreeSum.TernaryWantedDictionaryFiber
theorem _root_.solution (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) (C : ℕ)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) (J : ℕ) (x : ℤ) :
    ((values p raws J).filter (fun z => p^J ∣ x-z)).length ≤ C^J := by
  rw [filtered_values p hp,List.length_map]
  exact wantedOutputs_length_le p raws C hcap J x
end ThreeSum.TernaryWantedDictionaryFiber
