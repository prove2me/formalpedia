-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isChart_of_map_ff6e6ce7aa6c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:21:41.335001+00:00
-- url     : https://prove2.me/submissions/26fceac1-84b3-426b-9f0c-7fa21cbd693e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemMinimalPrimesOfMemDivSuppDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Antisymmetric_PNefOnFibresRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_RelabelTransport
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Targets_Relabel_X_mem_map_iff_71b520a09701

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Targets GroundTheory.Heights₂.Heights.Targets.Relabel
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 GroundTheory.Heights₂.Heights
variable {F : Type*} [Field F] {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
  {K' : Type*} [Fintype K'] {ι' : K' → Type*} [∀ k, Fintype (ι' k)]
  (e : K ≃ K') (h : ∀ k, ι k ≃ ι' (e k))
namespace GroundTheory.Heights₂.Heights.Targets.Relabel
theorem _root_.solution {V : Ideal (MRingOver F ι)} {i' : ∀ k', ι' k'}
    (hi' : IsChart (V.map (ringEquiv F e h)) i') : IsChart V fun k => (h k).symm (i' (e k)) := by
  intro k hk
  apply hi' (e k)
  have := (X_mem_map_iff e h V k ((h k).symm (i' (e k)))).2 hk
  rwa [Equiv.apply_symm_apply] at this
end GroundTheory.Heights₂.Heights.Targets.Relabel
