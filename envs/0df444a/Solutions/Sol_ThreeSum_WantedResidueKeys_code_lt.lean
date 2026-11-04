-- Prove2me | solution 1 for ThreeSum.WantedResidueKeys.code_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:07:48.901195+00:00
-- url     : https://prove2.me/submissions/07768178-6ee8-46e6-b726-19217448e585

import Definitions.Def_Submission_ThreeSum_WantedPairs
import Definitions.Def_Submission_ThreeSum_LightSourceResidues
import Definitions.Def_Submission_ThreeSum_WantedResidueKeys
import Theorems.Thm_ThreeSum_LightSourceResidues_key_lt


set_option autoImplicit false
open ThreeSum ThreeSum.WantedResidueKeys
open Light
open scoped BigOperators
namespace ThreeSum.WantedResidueKeys
theorem _root_.solution {M : ℕ} (hM : 0 < M) (shift x : ℤ) : code M shift x < M :=
  LightSourceResidues.key_lt hM shift x
end ThreeSum.WantedResidueKeys
