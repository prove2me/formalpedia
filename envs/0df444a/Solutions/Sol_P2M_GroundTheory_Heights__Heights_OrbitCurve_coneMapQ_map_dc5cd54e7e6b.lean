-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:45:29.081966+00:00
-- url     : https://prove2.me/submissions/d2a712a3-45c3-47ee-86a4-2c7b04f322f8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G Algebra
noncomputable section
open GroundTheory.Heights₂.Heights.OrbitCurve
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.OrbitCurve
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) (f : MvPolynomial (Coord n) ℤ) :
    coneMapQ x (map (Int.castRingHom ℚ) f) = Geo.mConeMap (ι := blockIdx n) (flatCone x) f := by
  rw [← algebraMap_int_eq, coneMapQ, aeval_map_algebraMap]
  rfl
end GroundTheory.Heights₂.Heights.OrbitCurve
