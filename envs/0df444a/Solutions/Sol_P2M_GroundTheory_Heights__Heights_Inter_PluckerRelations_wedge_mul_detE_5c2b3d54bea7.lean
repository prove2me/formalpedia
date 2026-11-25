-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_wedge_mul_detE_5c2b3d54bea7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:14:24.700996+00:00
-- url     : https://prove2.me/submissions/2f91236c-9d58-46f0-82ff-a3fa390b27c6

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
noncomputable section
open GroundTheory.Heights₂.Heights.Inter.PluckerRelations
variable {D : ℕ} (S : ProjectiveLineBundle D)
namespace GroundTheory.Heights₂.Heights.Inter.PluckerRelations
theorem _root_.solution (k m : S.κ) (u w : S.E) :
    wedgeVal S k m * T.detE S.e u w = S.φ k u * S.φ m w - S.φ k w * S.φ m u := by
  rw [apply_eq S (S.φ k) u, apply_eq S (S.φ m) w, apply_eq S (S.φ k) w, apply_eq S (S.φ m) u]
  simp only [wedgeVal, T.detE]
  ring
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
