-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_mixedDisc_comp_perm_4fe32ebbcec2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:59:12.668871+00:00
-- url     : https://prove2.me/submissions/da9e39d7-267b-4c2d-9f81-428359845ce3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSwap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotLtLtOfMemMinimalPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {D : ℕ}
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (σ : Equiv.Perm (Fin D)) :
    mixedDisc (A ∘ σ) = mixedDisc A := by
  unfold mixedDisc
  congr 1
  refine Fintype.sum_equiv (Equiv.finsetCongr σ) _ _ fun S => ?_
  rw [Equiv.finsetCongr_apply, Finset.card_map, Finset.sum_map]
  rfl
end GroundTheory.Heights₂.Heights.Inter
