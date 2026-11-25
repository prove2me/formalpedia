-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_TorusInvariantLevi_row_le_91853da86e09
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:58:38.858972+00:00
-- url     : https://prove2.me/submissions/b7835e6f-5927-4c9e-b2a4-34d05255281f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PTorusInvLevi

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
theorem _root_.solution (z w : J → ℂ) (q : J) :
    ∑ l, ‖z q * w l - z l * w q‖ ^ 2 ≤ ∑ j, ∑ l, ‖z j * w l - z l * w j‖ ^ 2 :=
  Finset.single_le_sum (f := fun j => ∑ l, ‖z j * w l - z l * w j‖ ^ 2)
    (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ q)
end GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi
