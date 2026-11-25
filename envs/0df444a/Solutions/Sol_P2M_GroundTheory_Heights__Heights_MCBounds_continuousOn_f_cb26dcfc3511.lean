-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCBounds_continuousOn_f_cb26dcfc3511
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:31.822067+00:00
-- url     : https://prove2.me/submissions/2298ac1f-f40e-431c-bee4-75021baaf28a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_DetIneq
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_BoundsY
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MatrixCharts_Bounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.MCBounds
open Matrix
open scoped ComplexOrder
noncomputable section
variable (D : PeriodChartData)
namespace GroundTheory.Heights₂.Heights.MCBounds
theorem _root_.solution : ContinuousOn D.f (D.U ×ˢ D.V) := by
  rw [continuousOn_iff_continuous_domRestrict]
  exact continuous_matrix fun j k => (D.f_analytic j k).continuousOn.domRestrict
end GroundTheory.Heights₂.Heights.MCBounds
