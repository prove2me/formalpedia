-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.left_mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:55:04.696858+00:00
-- url     : https://prove2.me/submissions/17bd0ab3-eec8-4643-a2e8-ffd98f530bf5

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
theorem _root_.solution {α π : DigitType} (e : LocalEdge L α π) :
    left e ∈ vertices L α := by
  classical
  exact mem_filter.mpr ⟨mem_univ _, (edge_data e).1⟩
end ThreeSum.TernaryCoverLocal
