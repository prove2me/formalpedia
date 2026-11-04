-- Prove2me | solution 1 for ThreeSum.TernaryCanonicalDictionaries.mapCode_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:04:34.201005+00:00
-- url     : https://prove2.me/submissions/11f2aa2d-877f-4597-945c-a91c07881aab

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
theorem _root_.solution (r : SourceRecord L α I) : |mapCode r| ≤ (Fintype.card I : ℤ) := by
  unfold mapCode
  rw [abs_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Fintype.equivFin I r.1).isLt.le
end ThreeSum.TernaryCanonicalDictionaries
