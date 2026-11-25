-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartEval_X_chart_5274b6332030
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:06:19.299529+00:00
-- url     : https://prove2.me/submissions/ff62659f-a8c2-4fd5-baa1-1c64bc6b97cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMult
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartQuot
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMultLemmas
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_injective_5ff86a6625e6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMult_chartIncl_chartEval_X_ff9f459061a4

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
theorem _root_.solution (hc : ∀ k, x k (c k) ≠ 0) (k : ι) :
    chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply chartIncl_injective x c
  rw [chartIncl_chartEval_X, map_one]
  exact div_self (hc k)
end GroundTheory.Heights₂.Heights.OrbitChartMult
