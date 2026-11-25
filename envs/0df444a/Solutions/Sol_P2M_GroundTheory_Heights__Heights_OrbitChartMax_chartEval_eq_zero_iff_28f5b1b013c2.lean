-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_chartEval_eq_zero_iff_28f5b1b013c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:03:21.076802+00:00
-- url     : https://prove2.me/submissions/9798517f-3d97-460c-86a3-f0f8b155d1a8

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
    (F : MvPolynomial (Coord n) ℤ) :
    chartEval x c F = 0 ↔ aeval (dehomCoords (flatCone x) c) F = 0 := by
  rw [← coe_chartEval, ZeroMemClass.coe_eq_zero, ZeroMemClass.coe_eq_zero]
end GroundTheory.Heights₂.Heights.OrbitChartMax
