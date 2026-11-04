-- Prove2me | solution 1 for ThreeSum.TernaryWantedDictionaryFiber.flatMap_range_getD
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:06:29.409029+00:00
-- url     : https://prove2.me/submissions/2540e8cc-c37d-46f0-9984-2a621f472030

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_map_range_getD


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers
namespace ThreeSum.TernaryWantedDictionaryFiber
theorem _root_.solution (xs : List ℤ) {A : Type*} (f : ℤ → List A) :
    xs.flatMap f=(List.range xs.length).flatMap (fun i => f (xs.getD i 0)) := by
  conv_rhs => rw [← List.flatMap_map,map_range_getD]
end ThreeSum.TernaryWantedDictionaryFiber
