-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.field_endpoint_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:59:39.182062+00:00
-- url     : https://prove2.me/submissions/32110b9c-c7bc-4a06-b282-87b7b997e797

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_endpoint_injective
import Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π => (fieldLeft (p := p) e, fieldRight (p := p) e)) := by
  intro e f he
  apply endpoint_injective α π
  exact Prod.ext (fieldWord_injective hp (congrArg Prod.fst he))
    (fieldWord_injective hp (congrArg Prod.snd he))
end ThreeSum.TernaryCoverLocal
