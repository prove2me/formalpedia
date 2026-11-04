-- Prove2me | solution 1 for ThreeSum.LightBoxStages.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:47.982077+00:00
-- url     : https://prove2.me/submissions/c47fbbfd-73d5-4c45-a3b4-0a23b1a310c2

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_BoxStages
import Definitions.Def_Submission_ThreeSum_LightBoxStages

set_option autoImplicit false
open ThreeSum ThreeSum.LightBoxStages
open Light ThreeSum.SubsetAddress ThreeSum.BoxStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightBoxStages
theorem _root_.solution : LightSubsetSetup.Procs program 6 7 8 9 10 11 12 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightBoxStages
