-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_regLine_a_dcb8ccb69f0f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:21:45.968951+00:00
-- url     : https://prove2.me/submissions/51e6c129-9b67-4d9d-9e65-bb4b31671555

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedC
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_IsMultiHomogPlaneCoordinate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
open scoped ContDiff
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Targets
theorem _root_.solution (A : HermLine ι) (s : MRing ι) (ε : ℝ) {a : K → ℕ} (ha : ∀ k, A.a k = a k)
    (hs : IsMultiHomog s a) : (regLine A s ε ha hs).a = 0 := rfl
end GroundTheory.Heights₂.Heights.Targets
