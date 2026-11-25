-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_log_norm_of_analytic_63c35a4f4a91
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:36.295315+00:00
-- url     : https://prove2.me/submissions/c15a3457-ac75-4605-aee1-6a925fbf983a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCPsh
open Metric Filter Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {h : ℂ → ℂ}
    (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    CircleIntegrable (fun ζ => Real.log ‖h ζ‖) 0 1 := by
  have : MeromorphicOn h (sphere (0:ℂ) |(1:ℝ)|) :=
    (hh.mono (by simpa using sphere_subset_closedBall)).meromorphicOn
  exact this.circleIntegrable_log_norm
end GroundTheory.Heights₂.Heights.MCPsh
