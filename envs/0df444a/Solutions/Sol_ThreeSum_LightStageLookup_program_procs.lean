-- Prove2me | solution 1 for ThreeSum.LightStageLookup.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:58:30.378002+00:00
-- url     : https://prove2.me/submissions/645c4d38-11c7-449e-9ca5-689e530f5f43

import Definitions.Def_Submission_ThreeSum_LightZetaStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages
import Definitions.Def_Submission_ThreeSum_LightDownsetAddress
import Definitions.Def_Submission_ThreeSum_LightStageLookup

set_option autoImplicit false
open ThreeSum ThreeSum.LightStageLookup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightStageLookup
theorem _root_.solution : LightSubsetSetup.Procs program 3 4 5 6 7 8 9 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightStageLookup
