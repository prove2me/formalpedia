-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitChartMax_coe_chartEval_a33db4734042
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:26:28.340079+00:00
-- url     : https://prove2.me/submissions/c61c4636-2737-4989-b0dc-34007af7e75a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartMax
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_PSubringPrimeMaximal
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMinimalPrimeMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartMax

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
    (((chartEval x c F : ratioField x) : AlgebraicClosure ℚ)) =
      aeval (dehomCoords (flatCone x) c) F := by
  induction F using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => rw [map_add, Subalgebra.coe_add, IntermediateField.coe_add, hp, hq, map_add]
  | mul_X p q hp =>
    rw [map_mul, Subalgebra.coe_mul, IntermediateField.coe_mul, hp, map_mul]
    simp [chartEval, chartRatio, dehomCoords, flatCone, div_eq_inv_mul]
end GroundTheory.Heights₂.Heights.OrbitChartMax
