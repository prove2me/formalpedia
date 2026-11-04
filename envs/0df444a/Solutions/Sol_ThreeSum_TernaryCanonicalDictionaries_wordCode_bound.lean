-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalDictionaries.wordCode_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:23:41.434364+00:00
-- url     : https://prove2.me/submissions/5b2cfcb6-5851-4640-8fbb-22b05bdb56c1

import Definitions.Def_Submission_ThreeSum_TernaryFixedDictionaries
import Definitions.Def_Submission_ThreeSum_LightTernaryParallelDictionaries
import Definitions.Def_Submission_ThreeSum_TernaryWantedLittleEndian
import Definitions.Def_Submission_ThreeSum_TernaryBankEnumeration
import Definitions.Def_Submission_ThreeSum_TernaryCanonicalDictionaries
import Theorems.Thm_ThreeSum_TernaryCanonicalDictionaries_wordCode_lt

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCanonicalDictionaries
open Finset Light RadixKeyLists TernaryFixedDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]
namespace ThreeSum.TernaryCanonicalDictionaries
theorem _root_.solution (r : SourceRecord L α I) : |wordCode r| ≤ (4^L : ℕ) := by
  unfold wordCode at *
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact (wordCode_lt r).le
end ThreeSum.TernaryCanonicalDictionaries
