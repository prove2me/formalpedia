-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_pointIdeal_map_rename_f76916d7d583
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:43:03.193901+00:00
-- url     : https://prove2.me/submissions/25f9a0e0-8154-4101-af01-025a7a1480bd

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosure
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagIndependence
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsVerticalDivisorJoinPullback
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsSegreFlagClosureBirational
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagIndependenceAlgebra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PSegreFlagClosurePullback

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K₁ K₂ : Type*} {ι₁ : K₁ → Type*} {ι₂ : K₂ → Type*} {R Φ : Type*} [CommRing R]
    [Field Φ] [Algebra R Φ] (e : K₁ ≃ K₂) (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k)) (hσ : ∀ v, (σ v).1 = e v.1)
    (y : (Σ k, ι₂ k) → Φ) : (pointIdeal R (y ∘ σ)).map (rename σ) = pointIdeal R y := by
  have key : ∀ f, pointConeMap R y (rename σ f) = rename e (pointConeMap R (y ∘ σ) f) := by
    intro f
    have h : (pointConeMap R y).toRingHom.comp (rename σ).toRingHom =
        (rename e).toRingHom.comp (pointConeMap R (y ∘ σ)).toRingHom := by
      apply MvPolynomial.ringHom_ext
      · intro a
        simp [pointConeMap, MvPolynomial.algebraMap_eq]
      · intro v
        simp [pointConeMap, hσ]
    have := RingHom.congr_fun h f
    simpa using this
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap]
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    rw [key, hf, map_zero]
  · intro f hf
    have hf' : rename σ (rename σ.symm f) = f := by
      rw [rename_rename]
      simp
    rw [← hf']
    apply Ideal.mem_map_of_mem
    simp only [pointIdeal, RingHom.mem_ker] at hf ⊢
    apply rename_injective _ e.injective
    rw [map_zero, ← key, hf', hf]
end GroundTheory.Heights₂.Heights.NumbersDVR
