-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_X_chart_91b55cfac444
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:41:31.586114+00:00
-- url     : https://prove2.me/submissions/782b9898-007a-4741-99d6-84f0a52ba9f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitChartMax_coe_chartEval_a33db4734042

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
open GroundTheory.Heights₂.Heights.OrbitChartMax
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitChartMax
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (c : (k : ι) → Fin (n k + 1))
    (hxc : ∀ k, flatCone x ⟨k, c k⟩ ≠ 0) (k : ι) : chartEval x c (X ⟨k, c k⟩) = 1 := by
  apply Subtype.ext
  apply Subtype.ext
  rw [coe_chartEval]
  simp [dehomCoords, inv_mul_cancel₀ (hxc k)]
end GroundTheory.Heights₂.Heights.OrbitChartMax
