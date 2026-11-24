-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Targets_Relabel_isRelevant_map_iff_e8200a2a6c10
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:22.752572+00:00
-- url     : https://prove2.me/submissions/b38573a7-7ecb-4088-b9ea-4eddbda34888

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
theorem _root_.solution (V : Ideal (MRingOver F ι)) :
    IsRelevant (V.map (ringEquiv F e h)) ↔ IsRelevant V := by
  constructor
  · intro hV k
    obtain ⟨i', hi'⟩ := hV (e k)
    refine ⟨(h k).symm i', fun hmem => hi' ?_⟩
    have := (X_mem_map_iff e h V k _).2 hmem
    rwa [Equiv.apply_symm_apply] at this
  · intro hV k'
    obtain ⟨k, rfl⟩ := e.surjective k'
    obtain ⟨i, hi⟩ := hV k
    exact ⟨h k i, fun hmem => hi ((X_mem_map_iff e h V k i).1 hmem)⟩
end GroundTheory.Heights₂.Heights.Targets.Relabel
