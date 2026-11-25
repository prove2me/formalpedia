-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_pointFormEuler_holds_leviOf_I_smul_right_1b7eb63621a8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:59:07.157529+00:00
-- url     : https://prove2.me/submissions/f58b885d-8da7-4579-b3d4-ef88c0600e53

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
theorem _root_.solution (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    leviOf H u (Complex.I • v) = -Complex.I * leviOf H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [leviOf, h, map_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring
end GroundTheory.Heights₂.Heights.Inter.pointFormEuler_holds
