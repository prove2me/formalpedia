-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_sum_right_ebed156926f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:11.287399+00:00
-- url     : https://prove2.me/submissions/ffd8c93b-10a4-44ef-94a8-7bfa8567a393

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ExMap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSheet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_LeviOfRealSmulRight
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_add_right_4973c981d991

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
theorem _root_.solution (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    leviOf H u (∑ j, v j) = ∑ j, leviOf H u (v j) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have h0 : leviOf H u 0 = 0 := by simp [leviOf]
    simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, leviOf_add_right, ih]
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
