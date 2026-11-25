-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCChartGradient_u_eq_daf79c38bffd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:18:28.101576+00:00
-- url     : https://prove2.me/submissions/4040ffea-50b6-4b15-aed4-dbda62a35114

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_StatementsBounds
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_PChartGradient

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
open Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.MCChartGradient
namespace GroundTheory.Heights₂.Heights.MCChartGradient
theorem _root_.solution (D : PeriodChartData) :
    D.u = fun q => logDetGram (D.Y q.1) (D.f q) := rfl
end GroundTheory.Heights₂.Heights.MCChartGradient
