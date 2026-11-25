-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_continuous_splitCoord_be4ce8002feb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:26:25.835933+00:00
-- url     : https://prove2.me/submissions/251b392c-4528-486e-9552-60e8730fe7d4

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
theorem _root_.solution (n m : ℕ) : Continuous (splitCoord n m) :=
  Continuous.prodMk (continuous_pi fun _ => continuous_apply _)
    (continuous_pi fun _ => continuous_apply _)
end GroundTheory.Heights₂.Heights
