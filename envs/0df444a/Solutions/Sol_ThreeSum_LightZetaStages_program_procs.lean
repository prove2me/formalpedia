-- Prove2me | solution 1 for ThreeSum.LightZetaStages.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:51:46.795263+00:00
-- url     : https://prove2.me/submissions/36c88731-e65f-4615-bbab-83fbfc6eec60

import Definitions.Def_Submission_ThreeSum_LightZetaPass
import Definitions.Def_Submission_ThreeSum_LightDownsetSize
import Definitions.Def_Submission_ThreeSum_SubsetStages
import Definitions.Def_Submission_ThreeSum_LightZetaStages

set_option autoImplicit false
open ThreeSum ThreeSum.LightZetaStages
open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightZetaStages
theorem _root_.solution : LightSubsetSetup.Procs program 6 7 8 9 10 11 12 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightZetaStages
