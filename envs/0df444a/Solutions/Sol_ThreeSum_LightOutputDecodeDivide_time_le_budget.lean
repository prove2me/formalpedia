-- Prove2me | solution 1 for ThreeSum.LightOutputDecodeDivide.time_le_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:40:17.643905+00:00
-- url     : https://prove2.me/submissions/f4b5025e-7451-4648-bc2c-9b985cca7a78

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Emod
import Definitions.Def_Submission_ThreeSum_LightOutputDecodeDivide
import Theorems.Thm_Light_emodRounds_le


set_option autoImplicit false
open ThreeSum ThreeSum.LightOutputDecodeDivide
open Light Light.Emod
set_option maxHeartbeats 1800000
set_option maxRecDepth 7000
variable {lim : Limits} {P : Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}
namespace ThreeSum.LightOutputDecodeDivide
theorem _root_.solution {a Mo V : ℕ} (ha : a ≤ V) : time a Mo ≤ budget V := by
  have hh := emodRounds_le ha (M := Mo)
  unfold time budget
  omega
end ThreeSum.LightOutputDecodeDivide
