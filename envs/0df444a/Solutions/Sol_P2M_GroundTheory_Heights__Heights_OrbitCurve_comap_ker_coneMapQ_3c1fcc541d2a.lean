-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrbitCurve_comap_ker_coneMapQ_3c1fcc541d2a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:29:48.040849+00:00
-- url     : https://prove2.me/submissions/e1a7a77f-dd43-4ba2-9fd4-09e398e9f064

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightOrbitCurve
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRat
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_POrbitCurve
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_OrbitCurve_coneMapQ_map_dc5cd54e7e6b

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
theorem _root_.solution (x : Cone n (AlgebraicClosure ℚ)) :
    (RingHom.ker (coneMapQ x)).comap (map (Int.castRingHom ℚ)) = orbitIdeal x := by
  ext f
  rw [Ideal.mem_comap, RingHom.mem_ker, coneMapQ_map, orbitIdeal, Geo.mCoordIdeal, RingHom.mem_ker]
end GroundTheory.Heights₂.Heights.OrbitCurve
