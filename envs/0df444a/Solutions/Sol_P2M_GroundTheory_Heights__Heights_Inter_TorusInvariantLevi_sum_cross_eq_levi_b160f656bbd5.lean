-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_cross_eq_levi_b160f656bbd5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:56:46.549969+00:00
-- url     : https://prove2.me/submissions/25f140c0-a143-4ee1-85a6-94a26ee345ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_sum_sum_normSq_cross_335fa3fae6c5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb


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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
set_option linter.unusedSectionVars false
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
theorem _root_.solution {z : J → ℂ} (hS : sqSum z ≠ 0) (w : J → ℂ) :
    ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 = 4 * sqSum z ^ 2 * leviForm phi z w := by
  rw [sum_sum_normSq_cross, leviForm_phi hS w]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
