-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_PluckerRelations_apply_eq_88396f4fe788
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:30:43.902168+00:00
-- url     : https://prove2.me/submissions/57e1eb1c-1683-4c40-9b83-3dc7b16f4179

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_XiPluckerRel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRFormula
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PPluckerRel

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
theorem _root_.solution (ψ : S.E →ₗ[S.Ω] S.Ω) (u : S.E) :
    ψ u = S.e.repr u 0 * ψ (S.e 0) + S.e.repr u 1 * ψ (S.e 1) := by
  have h := congrArg ψ (S.e.sum_repr u)
  rw [Fin.sum_univ_two, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul] at h
  exact h.symm
end GroundTheory.Heights₂.Heights.Inter.PluckerRelations
