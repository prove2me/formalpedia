-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_splitCoord_add_smul_a359f88157f1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:40:44.356533+00:00
-- url     : https://prove2.me/submissions/a0f37adf-83d3-4d92-8350-b4ba3c3805d8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PshMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartPotentialPsh

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix Metric Real MCPsh
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (n m : ℕ) (z w : Fin (n + m) → ℂ) (ζ : ℂ) :
    splitCoord n m (z + ζ • w) = splitCoord n m z + ζ • splitCoord n m w := by
  ext <;> simp [splitCoord]
end GroundTheory.Heights₂.Heights
