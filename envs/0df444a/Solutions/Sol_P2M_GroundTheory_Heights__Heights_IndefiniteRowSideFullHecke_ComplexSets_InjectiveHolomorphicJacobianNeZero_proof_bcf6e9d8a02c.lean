-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_proof_bcf6e9d8a02c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:58:26.803274+00:00
-- url     : https://prove2.me/submissions/c05454e9-7437-4eef-a8bc-5b8fb27478f3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicJacobianNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Filter Topology
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
namespace InjectiveHolomorphicJacobianNeZero
theorem _root_.solution (hF : HolomorphicKernelFibre.Statement)
    (hC : CriticalFlatNotInjective.Statement) : InjectiveHolomorphicJacobianNeZero.Statement := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro U f hU hf hinj x hx hdet
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · rw [LinearMap.det_eq_one_of_subsingleton] at hdet
      exact one_ne_zero hdet
    · exact InjectiveHolomorphicJacobianNeZero.one hU hf hinj hx hdet
  · by_cases hall : ∀ b ∈ U, LinearMap.det (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) = 0 →
        fderiv ℂ f b = 0
    · exact hC k U f x hk hU hf hx hdet hall hinj
    push Not at hall
    obtain ⟨b, hb, hdb, hne⟩ := hall
    set d := Module.finrank ℂ (LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ)) with hd
    have hd0 : 0 < d := by
      rw [hd, Module.finrank_pos_iff_exists_ne_zero]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (LinearMap.bot_lt_ker_of_det_eq_zero hdb).ne'
      exact ⟨⟨v, hv⟩, by simpa using hv0⟩
    have hdk : d < k := by
      have hker : LinearMap.ker (fderiv ℂ f b : (Fin k → ℂ) →ₗ[ℂ] Fin k → ℂ) ≠ ⊤ := by
        rw [Ne, LinearMap.ker_eq_top]
        intro h0
        exact hne (ContinuousLinearMap.coe_injective (by simpa using h0))
      simpa [Module.finrank_fin_fun] using Submodule.finrank_lt hker
    obtain ⟨V, y, γ, ℓ, hV, hy, hγ, hmaps, hγinj, hfib, hzero⟩ := hF k U f b hU hf hb d rfl
    have hhd : DifferentiableOn ℂ (fun t => ℓ (f (γ t))) V :=
      ℓ.differentiable.comp_differentiableOn (hf.comp hγ hmaps)
    have hhinj : Set.InjOn (fun t => ℓ (f (γ t))) V := fun s hs t ht h =>
      hγinj hs ht (hinj (hmaps hs) (hmaps ht) (hfib s hs t ht h))
    apply ih d hdk V _ hV hhd hhinj y hy
    rw [hzero, ContinuousLinearMap.toLinearMap_zero, LinearMap.det_zero, Module.finrank_fin_fun]
    exact zero_pow hd0.ne'
end InjectiveHolomorphicJacobianNeZero
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
