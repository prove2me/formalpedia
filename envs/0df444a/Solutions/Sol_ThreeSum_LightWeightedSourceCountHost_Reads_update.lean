-- Prove2me | solution 1 for ThreeSum.LightWeightedSourceCountHost.Reads.update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:23:11.051255+00:00
-- url     : https://prove2.me/submissions/4280e31e-5df5-4842-b95a-e0310bcfbadc

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_Weighted_CountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_Weighted_SourceCountHost
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightWeightedSourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightWeightedSourceCountHost
namespace Reads
theorem _root_.solution {loc : ℕ → ℤ} {offset x : ℕ} {vals : List ℤ}
    (h : Reads loc offset vals) (hx : offset+vals.length≤x) (r : ℤ) :
    Reads (Function.update loc x r) offset vals := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi
end Reads
end ThreeSum.LightWeightedSourceCountHost
