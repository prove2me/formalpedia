-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:35.076097+00:00
-- url     : https://prove2.me/submissions/b47b2663-113a-49b8-9b14-52f09abe059d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean

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
open Metric Real
noncomputable section
namespace GroundTheory.Heights₂.Heights.MCPsh
theorem _root_.solution {h : ℂ → ℂ} (hh : AnalyticOnNhd ℂ h (closedBall 0 1)) :
    circleAverage h 0 1 = h 0 := by
  apply DiffContOnCl.circleAverage
  apply DifferentiableOn.diffContOnCl
  rw [closure_ball _ (by norm_num : |(1:ℝ)| ≠ 0), abs_one]
  exact hh.differentiableOn
end GroundTheory.Heights₂.Heights.MCPsh
