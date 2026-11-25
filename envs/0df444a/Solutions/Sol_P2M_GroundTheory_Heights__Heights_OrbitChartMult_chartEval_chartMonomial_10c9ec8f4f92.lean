-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_chartMonomial_10c9ec8f4f92
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:28:52.265745+00:00
-- url     : https://prove2.me/submissions/f815c2eb-f276-436e-8ba4-ab2593de0cd8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030

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
variable [Fintype ι] [DecidableEq ι]
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMult
theorem _root_.solution (hc : ∀ k, x k (c k) ≠ 0) (d : ι → ℕ) :
    chartEval x c (chartMonomial c d) = 1 := by
  simp [chartMonomial, map_prod, chartEval_X_chart x c hc]
end GroundTheory.Heights₂.Heights.OrbitChartMult
