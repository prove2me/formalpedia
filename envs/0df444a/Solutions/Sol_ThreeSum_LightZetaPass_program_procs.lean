-- Prove2me | solution 1 for ThreeSum.LightZetaPass.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:45:29.921603+00:00
-- url     : https://prove2.me/submissions/179b9295-d61f-4a1f-b826-6d8f861c8104

import Definitions.Def_Submission_ThreeSum_LightZetaBatch
import Definitions.Def_Submission_ThreeSum_LightSubsetEnumerationSetup
import Definitions.Def_Submission_ThreeSum_LightZetaPass

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaPass
open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaPass
theorem _root_.solution : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightZetaPass
