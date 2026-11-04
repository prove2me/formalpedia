-- Prove2me | solution 1 for ThreeSum.LightDownsetAddress.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:39:24.984623+00:00
-- url     : https://prove2.me/submissions/427e21d0-1fc8-49f9-b34b-739955cc2cd1

import Definitions.Def_Submission_ThreeSum_LightSubsetSetup
import Definitions.Def_Submission_ThreeSum_LightSubsetOffset
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress

set_option autoImplicit false
open ThreeSum ThreeSum.LightDownsetAddress
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightDownsetAddress
theorem _root_.solution : LightSubsetSetup.Procs program 1 2 3 4 5 6 7 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightDownsetAddress
