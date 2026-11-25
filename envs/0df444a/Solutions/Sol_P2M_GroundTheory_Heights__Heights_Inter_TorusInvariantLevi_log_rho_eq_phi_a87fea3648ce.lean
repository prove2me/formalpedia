-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_log_rho_eq_phi_a87fea3648ce
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:59:02.239236+00:00
-- url     : https://prove2.me/submissions/70c2e614-afd9-4272-93ec-4baecb0ea424

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_sqSum_nonneg_41101420cfdf


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
theorem _root_.solution (x : J → ℂ) : Real.log ((fsMetric J).ρ x) = phi x := by
  have h : (fsMetric J).ρ x = Real.sqrt (sqSum x) := by
    simp [fsMetric, EuclideanSpace.norm_eq, sqSum]
  rw [h, Real.log_sqrt (sqSum_nonneg x), phi]
  ring
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
