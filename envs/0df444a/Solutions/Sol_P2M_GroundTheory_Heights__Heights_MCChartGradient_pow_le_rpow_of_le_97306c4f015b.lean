-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_MCChartGradient_pow_le_rpow_of_le_97306c4f015b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:04:42.971155+00:00
-- url     : https://prove2.me/submissions/231d52c4-2ace-4267-ac88-59fa6613e6cf

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
theorem _root_.solution {r C : ℝ} {k : ℕ} (hr : 1 ≤ r) (hk : (k : ℝ) ≤ C) :
    r ^ k ≤ r ^ C := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le hr hk
end GroundTheory.Heights₂.Heights.MCChartGradient
