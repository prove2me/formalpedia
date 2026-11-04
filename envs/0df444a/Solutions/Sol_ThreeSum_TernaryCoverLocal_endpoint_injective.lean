-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:55:01.984239+00:00
-- url     : https://prove2.me/submissions/336bfe10-248e-441e-bd5c-9e097922ce91

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_edge_data

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType) :
    Function.Injective (fun e : LocalEdge L α π => (left e, right e)) := by
  intro e f he
  have hl : left e = left f := congrArg (fun z : TritWord L × TritWord L => z.1) he
  have hr : right e = right f := congrArg (fun z : TritWord L × TritWord L => z.2) he
  have hq : output e = output f := by
    funext i
    apply Fin.ext
    have hs := (edge_data e).2.2.2 i
    have ht := (edge_data f).2.2.2 i
    rw [hl, hr] at hs
    exact hs.symm.trans ht
  apply Subtype.ext
  exact Prod.ext hl (Prod.ext hr hq)
end ThreeSum.TernaryCoverLocal
