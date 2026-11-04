-- Prove2me | solution 1 for ThreeSum.TernarySolverEndBridge.powerBound_of_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T12:07:59.680423+00:00
-- url     : https://prove2.me/submissions/de6c251d-b57e-4404-a6de-c2fe98a721d8

import Definitions.Def_Submission_ThreeSum_TernaryHybridCosts
import Definitions.Def_Submission_ThreeSum_TernarySolverEndBridge
import Theorems.Thm_ThreeSumApsp_Dominated_trans
import Theorems.Thm_ThreeSumApsp_WordRam_AgreeOutside_trans
import Theorems.Thm_ThreeSumApsp_WordRam_Steps_trans


set_option autoImplicit false
noncomputable section
open ThreeSum ThreeSum.TernarySolverEndBridge
open Light Filter StageBounds
open scoped Topology
set_option maxHeartbeats 1500000
set_option maxRecDepth 16000
namespace ThreeSum.TernarySolverEndBridge
theorem _root_.solution {T : ℕ→ ℕ} {a : ℝ}
    (ht : ∀ᶠ n : ℕ in atTop, (T n:ℝ)≤ (n:ℝ)^a) : PowerBound T a := by
  intro δ hδ
  filter_upwards [ht,eventually_ge_atTop (1:ℕ)] with n hn h1
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast h1) (by linarith))
end ThreeSum.TernarySolverEndBridge
