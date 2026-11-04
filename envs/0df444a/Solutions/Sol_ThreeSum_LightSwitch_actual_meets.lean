-- Prove2me | solution 1 for ThreeSum.LightSwitch.actual_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:12.564742+00:00
-- url     : https://prove2.me/submissions/38a1f14f-cf70-4452-af0b-90e66e0ca003

import Definitions.Def_Submission_ThreeSum_LightSwitchBounds
import Definitions.Def_Submission_ThreeSum_LightSwitchScalar
import Definitions.Def_Submission_ThreeSum_LightSwitch
import Theorems.Thm_ThreeSum_LightSwitch_program_meets
import Theorems.Thm_ThreeSum_LightSwitch_actual_candidates_nonempty
import Theorems.Thm_ThreeSum_Scales_actual_candidates_nonempty
import Theorems.Thm_ThreeSum_Switch_actual_depth_condition


set_option autoImplicit false
open ThreeSum ThreeSum.LightSwitch
open Light
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}
namespace ThreeSum.LightSwitch
theorem _root_.solution {n j : ℕ} (hj : j ≤ Switch.terminalDepth n)
    (hword : (word (Scales.blockCount (Scales.inputBits n))
      (Switch.residualSize n j) : ℤ) ≤ lim.word) :
    Meets lim program 0 d
      [Scales.blockCount (Scales.inputBits n),j,Switch.residualSize n j] μ
      (time (Switch.residualSize n j))
      (fun result ν => result=(Switch.actualSwitch n j : ℤ) ∧ ν=μ) := by
  have hdepth := Switch.actual_depth_condition hj
  exact program_meets (by omega) (actual_candidates_nonempty hj) hword
end ThreeSum.LightSwitch
