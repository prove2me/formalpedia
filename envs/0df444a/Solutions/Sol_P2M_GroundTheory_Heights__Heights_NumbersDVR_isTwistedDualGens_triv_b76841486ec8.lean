-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isTwistedDualGens_triv_b76841486ec8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:07:41.605478+00:00
-- url     : https://prove2.me/submissions/53081dd6-1321-4b18-97c5-b6f01721bbd7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_Bundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BundleObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
variable {Ω : Type*} [Field Ω] (R : Type*) [CommRing R] [Algebra R Ω] {τ : Type*}
variable {R}
variable (R)
variable {K : Type*} [Fintype K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (y : (Σ k, ι k) → Ω) (r : ℕ) :
    IsTwistedDualGens y (scaledTrivBundle R (segreVec y) r one_ne_zero) 0
      (fun l : Fin r => (LinearMap.proj l : Module.Dual Ω (Fin r → Ω))) where
  sections c hc l v hv := by
    obtain ⟨a, ha, hva⟩ := (mem_scaledTrivLat).1 hv l
    exact ⟨a, ha, by simp [hva]⟩
  generate c hc ψ hψ := by
    refine ⟨fun l => ψ (Pi.single l 1), fun l => hψ _ ((mem_scaledTrivLat).2 fun q => ?_), ?_⟩
    · by_cases h : q = l
      · subst h
        exact ⟨1, one_mem _, by simp⟩
      · exact ⟨0, zero_mem _, by simp [h]⟩
    · ext i
      simp [Pi.single_apply]
end GroundTheory.Heights₂.Heights.NumbersDVR
