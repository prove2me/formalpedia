-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.right_mem_vertices
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:55:05.772046+00:00
-- url     : https://prove2.me/submissions/413a69e2-418f-4aab-bb31-c682ba62066f

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
    right e ∈ vertices L α := by
  classical
  exact mem_filter.mpr ⟨mem_univ _, (edge_data e).2.1⟩
end ThreeSum.TernaryCoverLocal
