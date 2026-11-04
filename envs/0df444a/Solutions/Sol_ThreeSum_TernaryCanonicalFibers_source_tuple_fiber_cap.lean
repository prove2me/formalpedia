-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalFibers.source_tuple_fiber_cap
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:14.973067+00:00
-- url     : https://prove2.me/submissions/bdae93d0-3085-4ae1-83d2-8203a58bbffd

import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedRadix
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalFibers
import Theorems.Thm_ThreeSum_TernaryCanonicalFibers_local_native_cap
import Theorems.Thm_ThreeSum_TernaryWantedRadix_wantedOutputs_length_le


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalFibers
theorem _root_.solution (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (J : ℕ) (x : ℤ) :
    (TernaryWantedRadix.wantedOutputs (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) J x).length ≤
      (Fintype.card I*B)^J :=
  TernaryWantedRadix.wantedOutputs_length_le _ _ _ (local_native_cap right maps B hp) J x
end ThreeSum.TernaryCanonicalFibers
