-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.fieldRight_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:18.003223+00:00
-- url     : https://prove2.me/submissions/fa294105-3053-455c-b76d-51b14aacfc7f

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal
import Theorems.Thm_ThreeSum_TernaryCoverLocal_right_mem_vertices

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution {α π : DigitType} (e : LocalEdge L α π) :
    fieldRight (p := p) e ∈ fieldVertices L p α := by
  exact mem_image.mpr ⟨right e, right_mem_vertices e, rfl⟩
end ThreeSum.TernaryCoverLocal
