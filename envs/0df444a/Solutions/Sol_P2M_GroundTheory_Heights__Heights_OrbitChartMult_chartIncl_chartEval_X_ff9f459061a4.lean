-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:52:39.158308+00:00
-- url     : https://prove2.me/submissions/3fcc90a5-5000-4286-b6af-3bee8d48c5cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas

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
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitChartMult
variable {ι : Type} {n : ι → ℕ}
variable (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (p : Coord n) :
    chartIncl x c (chartEval x c (X p)) = x p.1 p.2 / x p.1 (c p.1) := by
  simp [chartIncl, chartEval, chartRatio]
end GroundTheory.Heights₂.Heights.OrbitChartMult
