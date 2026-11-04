-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalDictionaries.native_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:33.060092+00:00
-- url     : https://prove2.me/submissions/6492a9d1-c988-4a2c-a0a6-51c081bce49e

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalDictionaries
theorem _root_.solution (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) : |native right maps r| ≤ (p : ℤ) := by
  unfold native
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (ZMod.val_lt (if right then rightNative maps r else leftNative maps r)).le
end ThreeSum.TernaryCanonicalDictionaries
