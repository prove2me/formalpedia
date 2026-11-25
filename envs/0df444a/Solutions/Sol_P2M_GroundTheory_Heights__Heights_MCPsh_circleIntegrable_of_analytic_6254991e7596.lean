-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:20:37.516972+00:00
-- url     : https://prove2.me/submissions/c9f70027-27d4-4139-bba1-89cd08d2aa41

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
    CircleIntegrable h 0 1 :=
  (hh.continuousOn.mono sphere_subset_closedBall).circleIntegrable zero_le_one
end GroundTheory.Heights₂.Heights.MCPsh
