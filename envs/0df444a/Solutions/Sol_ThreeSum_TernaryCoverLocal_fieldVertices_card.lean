-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.fieldVertices_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:16.34401+00:00
-- url     : https://prove2.me/submissions/78b7434e-6054-4fb1-bd41-453f0506c214

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryJointType_fieldWord_injective


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution (α : DigitType) (hp : 2 < p) :
    (fieldVertices L p α).card = (vertices L α).card := by
  classical
  exact card_image_of_injective _ (fieldWord_injective hp)
end ThreeSum.TernaryCoverLocal
