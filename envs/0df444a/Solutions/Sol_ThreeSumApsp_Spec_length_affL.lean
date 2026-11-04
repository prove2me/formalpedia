-- Prove2me | solution 1 for ThreeSumApsp.Spec.length_affL
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:04:02.830203+00:00
-- url     : https://prove2.me/submissions/2e858e7e-40cc-4c55-9c28-06cf68983e00

import Definitions.Def_Submission_PaperStatements
import Definitions.Def_Submission_ThreeSumApsp_Util_Index
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Definitions.Def_Submission_ThreeSumApsp_Spec_Sec3_Problems

set_option autoImplicit false
section
open ThreeSumApsp ThreeSumApsp.Spec
namespace ThreeSumApsp.Spec
theorem _root_.solution (m c : ℤ) (l : List ℤ) : (affL m c l).length = l.length := by
  simp [affL]
end ThreeSumApsp.Spec
