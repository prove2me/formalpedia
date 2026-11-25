-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_coe_evalCone_coordVec_1ad214d3b804
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:58.607531+00:00
-- url     : https://prove2.me/submissions/209a9967-f938-40a0-bc66-048e8d7049e5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitChartTerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitChartTerm

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
variable {ι : Type} [Fintype ι] {n : ι → ℕ}
omit [Fintype ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (s : MvPolynomial (Coord n) ℤ) :
    ((evalCone (coordVec x) s : coordField x) : AlgebraicClosure ℚ) = evalCone x s := by
  have h := eval₂_comp_left (algebraMap (coordField x) (AlgebraicClosure ℚ)) (Int.castRingHom _)
    (fun v ↦ coordVec x v.1 v.2) s
  rw [RingHom.ext_int ((algebraMap (coordField x) (AlgebraicClosure ℚ)).comp (Int.castRingHom _))
    (Int.castRingHom _)] at h
  exact h
end GroundTheory.Heights₂.Heights
