-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:36.343259+00:00
-- url     : https://prove2.me/submissions/258a5dde-5e2d-40c5-b4fd-94ce99debd64

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
theorem _root_.solution (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v w : Fin n → ℂ) :
    leviOf H u (v + w) = leviOf H u v + leviOf H u w := by
  simp only [leviOf, smul_add, map_add]
  push_cast
  ring
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
