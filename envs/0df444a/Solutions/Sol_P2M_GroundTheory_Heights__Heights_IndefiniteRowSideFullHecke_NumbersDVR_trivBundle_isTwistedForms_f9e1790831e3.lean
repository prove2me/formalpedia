-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_trivBundle_isTwistedForms_f9e1790831e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:13:13.418666+00:00
-- url     : https://prove2.me/submissions/50fba92d-f85d-4fc1-91ff-91a9265a3e4f

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
    IsTwistedForms pt (trivBundle o (segreVec pt) N)
      (fun t : Fin N => (LinearMap.proj t : (Fin N → Ω) →ₗ[Ω] Ω)) 0 := by
  intro i _
  refine ⟨fun t e he => ⟨e t, mem_trivBundle.1 he t, by simp [chartMono_zero]⟩, fun ψ hψ => ?_⟩
  refine ⟨fun t => ψ (Pi.single t 1), fun t => hψ _ (single_mem_trivBundle t (one_mem _)), ?_⟩
  apply LinearMap.pi_ext
  intro s y
  have hs : (Pi.single s y : Fin N → Ω) = y • Pi.single s (1 : Ω) := by
    ext q
    by_cases h : q = s
    · subst h; simp
    · simp [h]
  rw [hs, map_smul]
  simp [chartMono_zero, LinearMap.sum_apply, Pi.single_apply, smul_eq_mul, mul_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR
