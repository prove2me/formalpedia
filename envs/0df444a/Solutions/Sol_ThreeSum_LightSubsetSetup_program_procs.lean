-- Prove2me | solution 1 for ThreeSum.LightSubsetSetup.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:33:11.986199+00:00
-- url     : https://prove2.me/submissions/4ef4809d-4627-4466-899d-2d8460f196ee

import Definitions.Def_Submission_ThreeSum_LightSubsetAddress
import Definitions.Def_Submission_ThreeSum_LightSubsetSetup

set_option autoImplicit false
open ThreeSum ThreeSum.LightSubsetSetup
open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightSubsetSetup
theorem _root_.solution : Procs program 0 1 2 3 4 5 6 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightSubsetSetup
