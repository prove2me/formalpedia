-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_im_of_analytic_28853a1159d6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:00:37.504692+00:00
-- url     : https://prove2.me/submissions/629f8428-35ca-46ad-90ab-6ac4d3159e78

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshCore
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleAverage_of_analytic_5753593141aa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_MCPsh_circleIntegrable_of_analytic_6254991e7596

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
    circleAverage (fun ζ => (h ζ).im) 0 1 = (h 0).im := by
  have := Complex.imCLM.circleAverage_comp_comm (circleIntegrable_of_analytic hh)
  rw [circleAverage_of_analytic hh] at this
  simpa [Function.comp_def] using this
end GroundTheory.Heights₂.Heights.MCPsh
