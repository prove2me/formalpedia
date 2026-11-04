-- Prove2me | solution 1 for ThreeSum.LightSignedLeaf.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:48.598612+00:00
-- url     : https://prove2.me/submissions/b03df55e-6fd4-48a7-bdd4-abb2d98855f4

import Definitions.Def_Submission_ThreeSum_SignedLeaf
import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightSign
import Definitions.Def_Submission_ThreeSum_LightSignedLeaf

set_option autoImplicit false
open ThreeSum ThreeSum.LightSignedLeaf
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSignedLeaf
theorem _root_.solution : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSignedLeaf
