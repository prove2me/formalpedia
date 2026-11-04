-- Prove2me | solution 1 for ThreeSum.LightTernarySourceCountHost.Reads.update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T13:17:19.72502+00:00
-- url     : https://prove2.me/submissions/f261564e-6e2c-4352-8846-4e2b719da875

import Definitions.Def_Submission_ThreeSum_LightTernarySourceHost
import Definitions.Def_Submission_ThreeSum_LightTernaryCountFrontend
import Definitions.Def_Submission_ThreeSum_TernarySourceHostModel
import Definitions.Def_Submission_ThreeSum_LightTernarySourceCountHost
import Theorems.Thm_Light_LocalsBut_update


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.LightTernarySourceCountHost
open Light
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
namespace ThreeSum.LightTernarySourceCountHost
namespace Reads
theorem _root_.solution {loc : ℕ → ℤ} {offset x : ℕ} {vals : List ℤ}
    (h : Reads loc offset vals) (hx : offset+vals.length≤x) (r : ℤ) :
    Reads (Function.update loc x r) offset vals := by
  intro i hi
  rw [Function.update_of_ne (by omega)]
  exact h i hi
end Reads
end ThreeSum.LightTernarySourceCountHost
