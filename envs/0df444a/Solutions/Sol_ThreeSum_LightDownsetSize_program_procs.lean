-- Prove2me | solution 1 for ThreeSum.LightDownsetSize.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:21.205224+00:00
-- url     : https://prove2.me/submissions/43f36431-2d5e-4d19-90c0-c7377870df9d

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetSize

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetSize
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetSize
theorem _root_.solution : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightDownsetSize
