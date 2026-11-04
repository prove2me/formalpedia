-- Prove2me | solution 1 for ThreeSum.LightQueryBox.program_procs
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T09:05:49.776372+00:00
-- url     : https://prove2.me/submissions/7e9339cf-ae12-4744-8d45-a684f1f8ffa1

import Definitions.Def_Submission_ThreeSum_LightStageLookup
import Definitions.Def_Submission_ThreeSum_LightMaskMinimum
import Definitions.Def_Submission_ThreeSum_MaskDifference
import Definitions.Def_Submission_ThreeSum_LightQueryBox

set_option autoImplicit false
open ThreeSum ThreeSum.LightQueryBox
open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress
variable {lim : Limits} {P : Program}
namespace ThreeSum.LightQueryBox
theorem _root_.solution : LightSubsetSetup.Procs program 5 6 7 12 13 8 9 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
end ThreeSum.LightQueryBox
