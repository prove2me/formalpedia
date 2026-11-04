-- Prove2me | solution 1 for ThreeSum.LightSignedLeafGeneral.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:36:32.342679+00:00
-- url     : https://prove2.me/submissions/afcffb0c-9da3-4333-af1f-d1a597e0f512

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightMaskUnion
import Definitions.Def_Submission_ThreeSum_LightSignedLeafGeneral

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeafGeneral
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeafGeneral
theorem _root_.solution : LightSubsetSetup.Procs program 5 6 7 8 9 10 11 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSignedLeafGeneral
