-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalFibers.local_native_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:20:06.469948+00:00
-- url     : https://prove2.me/submissions/18eff6f4-96a9-4511-af3c-e114bfbef0c1

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_localBucket_length
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_native_filter_cap

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalFibers
theorem _root_.solution (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    (TernaryWantedRadix.localBucket (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) x).length ≤ Fintype.card I*B := by
  rw [localBucket_length,List.filter_map,List.length_map]
  exact native_filter_cap right maps B hp x
end ThreeSum.TernaryCanonicalFibers
