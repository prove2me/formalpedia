-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isFlagGrading_b44ce4708f58
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:11:07.917658+00:00
-- url     : https://prove2.me/submissions/e87ee899-60ef-4df3-b48d-ba6a271d81b8

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_TrivBundleIsTwistedForms
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_mem_trivBundle_251b4824d13c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_single_mem_trivBundle_de483b7ea745
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_chartMono_zero_1b1fcd88d57b

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
open MvPolynomial Module ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
universe u v w u₁ u₂
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable (o : Type*) [CommRing o] {Ω : Type*} [Field Ω] [Algebra o Ω]
variable {o}
omit [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
theorem _root_.solution (pt : MRingOver o ι →ₐ[o] Ω) (N : ℕ) :
    IsFlagGrading pt (trivBundle o (segreVec pt) N) (Pi.basisFun Ω (Fin N)) 0 1 := by
  refine ⟨fun _ => one_ne_zero, fun i _ l => ?_⟩
  ext a
  simp only [gradedLat, degLine, Pi.basisFun_repr, Pi.zero_apply, chartMono_zero, mul_one,
    Pi.one_apply, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨e, he, -, rfl⟩
    exact ⟨e l, mem_trivBundle.1 he l, rfl⟩
  · rintro ⟨r, hr, hra⟩
    refine ⟨Pi.single l r, single_mem_trivBundle l hr, fun j hj => ?_, by simp [hra]⟩
    simp [ne_of_gt hj]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
