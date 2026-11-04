-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.fieldLeft_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:16.963659+00:00
-- url     : https://prove2.me/submissions/bce9a325-15c3-428e-93ef-6a17357aa851

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_left_mem_vertices

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution {α π : DigitType} (e : LocalEdge L α π) :
    fieldLeft (p := p) e ∈ fieldVertices L p α := by
  exact mem_image.mpr ⟨left e, left_mem_vertices e, rfl⟩
end ThreeSum.TernaryCoverLocal
