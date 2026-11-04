-- Prove2me | solution 1 for ThreeSum.LightLeafSum.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:13:50.364757+00:00
-- url     : https://prove2.me/submissions/a5d4a3a8-e86d-49fd-952e-8cc5e53b6f93

import Definitions.Def_Submission_ThreeSum_LightSignedLeaf
import Definitions.Def_Submission_ThreeSum_LightLeafSum

set_option autoImplicit false
open ThreeSum ThreeSum.LightLeafSum
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightLeafSum
theorem _root_.solution : LightSubsetSetup.Procs program 5 6 7 8 9 10 11 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightLeafSum
