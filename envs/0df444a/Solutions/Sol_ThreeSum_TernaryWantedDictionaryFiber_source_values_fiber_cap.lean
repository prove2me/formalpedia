-- Prove2me | solution 1 for ThreeSum.TernaryWantedDictionaryFiber.source_values_fiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:24:24.768975+00:00
-- url     : https://prove2.me/submissions/4cf5eb0a-5077-4052-a0ad-e438e1fa992a

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Definitions.Def_Submission_ThreeSum_TernaryWantedDictionaryFiber
import Theorems.Thm_ThreeSum_TernaryWantedDictionaryFiber_values_fiber_cap
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_local_native_cap


set_option autoImplicit false
open ThreeSum ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers
namespace ThreeSum.TernaryWantedDictionaryFiber
theorem _root_.solution {L p : ℕ} [Fact p.Prime]
    {α : TernaryJointType.DigitType} {I : Type*} [Fintype I] [DecidableEq I]
    (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2<p) (J : ℕ) (x : ℤ) :
    ((values (p : ℤ)
      ((TernaryCanonicalDictionaries.records (α := α) right maps B).map
        (TernaryCanonicalDictionaries.native right maps)) J).filter
      (fun z => (p : ℤ)^J ∣ x-z)).length ≤ (Fintype.card I*B)^J := by
  exact values_fiber_cap (p : ℤ) (by exact_mod_cast (by omega : p≠0)) _ _
    (local_native_cap right maps B hp) J x
end ThreeSum.TernaryWantedDictionaryFiber
