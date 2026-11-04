-- Prove2me | solution 1 for ThreeSum.TernaryCoverLocal.edge_data
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:47:15.349081+00:00
-- url     : https://prove2.me/submissions/e068957b-5325-47aa-9101-40c97ca0c961

import Definitions.Def_Submission_ThreeSum_TernaryJointType
import Definitions.Def_Submission_ThreeSum_TernaryCoverTrimming
import Definitions.Def_Submission_ThreeSum_TernaryCoverFibers
import Definitions.Def_Submission_ThreeSum_TernaryCoverRetained
import Definitions.Def_Submission_ThreeSum_TernaryCoverLocal

set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernaryCoverLocal
open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators
variable {L p : ℕ}
namespace ThreeSum.TernaryCoverLocal
theorem _root_.solution {α π : DigitType} (e : LocalEdge L α π) :
    Edge α π (left e) (right e) (output e) := by
  classical
  exact (mem_filter.mp e.property).2
end ThreeSum.TernaryCoverLocal
