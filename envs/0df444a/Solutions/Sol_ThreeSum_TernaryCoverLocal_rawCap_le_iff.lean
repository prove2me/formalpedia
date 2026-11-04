-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.rawCap_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:01:38.90389+00:00
-- url     : https://prove2.me/submissions/1f068d60-294b-4ba3-ab31-343712abdf1a

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_rawPairCount_le_rawCap

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
variable [Fact (Nat.Prime p)]
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType) (w : Coordinate (Fin L) → ZMod p) (τ : ℕ) :
    rawCap α π w ≤ τ ↔ ∀ a b : ZMod p,
      TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤ τ := by
  classical
  constructor
  · intro h a b
    exact (rawPairCount_le_rawCap α π w a b).trans h
  · intro h
    unfold rawCap
    apply Finset.sup_le
    intro t _
    exact h t.1 t.2
end ThreeSum.TernaryCoverLocal
