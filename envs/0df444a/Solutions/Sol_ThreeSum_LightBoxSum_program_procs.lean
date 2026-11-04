-- Prove2me | solution 1 for ThreeSum.LightBoxSum.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:14:28.084909+00:00
-- url     : https://prove2.me/submissions/d14c2cfe-fcf1-4bd8-ace9-96e018e1a1b5

import Definitions.Def_Submission_ThreeSum_LightQueryBox
import Definitions.Def_Submission_ThreeSum_BoxBounds
import Definitions.Def_Submission_ThreeSum_LightBoxSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxSum
theorem _root_.solution : LightSubsetSetup.Procs program 6 7 8 13 14 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBoxSum
