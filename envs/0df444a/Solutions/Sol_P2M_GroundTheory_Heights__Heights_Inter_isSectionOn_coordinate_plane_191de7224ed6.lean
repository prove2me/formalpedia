-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_isSectionOn_coordinate_plane_191de7224ed6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:58:52.533908+00:00
-- url     : https://prove2.me/submissions/f10aca8e-60a2-46b2-86d0-f9aa783ac6a3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo InnerProductSpace Laplacian
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (i : Fin 3) : IsSectionOn (⊥ : Ideal (MRing (PBlk 3))) (fsLine 3) (Xc 3 i) := by
  refine ⟨fun _ => 1, fun _ => rfl, fun m hm k => ?_, ?_⟩
  · rw [support_X, Finset.mem_singleton] at hm
    subst hm
    simp [Finsupp.single_apply]
  · rw [Submodule.mem_bot]
    exact X_ne_zero _
end GroundTheory.Heights₂.Heights.Inter
