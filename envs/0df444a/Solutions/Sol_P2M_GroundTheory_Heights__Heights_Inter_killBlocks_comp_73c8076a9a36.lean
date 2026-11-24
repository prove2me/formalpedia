-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_killBlocks_comp_73c8076a9a36
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:32.538055+00:00
-- url     : https://prove2.me/submissions/34ec165d-9da1-40a3-b7e5-f1c8a532a37f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_ThmISt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_UniquenessDegreeFormOfIntersectionForm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ArithVarZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_killBlocks_X_891fa96bfde9

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution {S S' : Set K} (h : S ⊆ S') :
    (killBlocks S').comp (killBlocks S) = (killBlocks S' : MRing ι →ₐ[ℤ] MRing ι) := by
  refine MvPolynomial.algHom_ext fun p => ?_
  rw [AlgHom.comp_apply, killBlocks_X, killBlocks_X]
  by_cases hp : p.1 ∈ S
  · rw [if_pos hp, map_zero, if_pos (h hp)]
  · rw [if_neg hp, killBlocks_X]
end GroundTheory.Heights₂.Heights.Inter
