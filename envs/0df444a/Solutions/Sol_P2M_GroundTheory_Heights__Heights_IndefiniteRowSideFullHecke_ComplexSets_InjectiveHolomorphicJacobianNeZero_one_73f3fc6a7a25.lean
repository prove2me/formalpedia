-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_one_73f3fc6a7a25
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:05:36.279822+00:00
-- url     : https://prove2.me/submissions/8eac0d39-03a1-4e26-95d0-20f00035ab62

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInjectiveHolomorphicJacobianNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicDerivNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StHolomorphicKernelFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCriticalFlatNotInjective
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicJacobianNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicJacobianNeZero_det_fin_one_8fe152a841bf
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_InjectiveHolomorphicDerivNeZero_proof_0e516cf86a2c


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
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
theorem _root_.solution {U : Set (Fin 1 → ℂ)} {f : (Fin 1 → ℂ) → Fin 1 → ℂ} (hU : IsOpen U)
    (hf : DifferentiableOn ℂ f U) (hinj : Set.InjOn f U) {x : Fin 1 → ℂ} (hx : x ∈ U) :
    LinearMap.det (fderiv ℂ f x : (Fin 1 → ℂ) →ₗ[ℂ] Fin 1 → ℂ) ≠ 0 := by
  set e : (Fin 1 → ℂ) ≃L[ℂ] ℂ := ContinuousLinearEquiv.funUnique (Fin 1) ℂ ℂ with he
  set φ : ℂ → ℂ := fun z => e (f (e.symm z)) with hφ
  have hD : IsOpen (e.symm ⁻¹' U) := hU.preimage e.symm.continuous
  have hφd : DifferentiableOn ℂ φ (e.symm ⁻¹' U) :=
    e.differentiable.comp_differentiableOn (hf.comp e.symm.differentiable.differentiableOn fun _ h => h)
  have hφi : Set.InjOn φ (e.symm ⁻¹' U) := fun s hs t ht h =>
    e.symm.injective (hinj hs ht (e.injective h))
  have hxD : e x ∈ e.symm ⁻¹' U := by simpa using hx
  have hne := InjectiveHolomorphicDerivNeZero.proof _ φ hD hφd hφi (e x) hxD
  have hfx : HasFDerivAt f (fderiv ℂ f x) x := (hf.differentiableAt (hU.mem_nhds hx)).hasFDerivAt
  have hφx : HasFDerivAt φ ((e : (Fin 1 → ℂ) →L[ℂ] ℂ).comp ((fderiv ℂ f x).comp
      (e.symm : ℂ →L[ℂ] Fin 1 → ℂ))) (e x) := by
    have h1 : HasFDerivAt f (fderiv ℂ f x) (e.symm (e x)) := by simpa using hfx
    exact e.hasFDerivAt.comp (e x) (h1.comp (e x) e.symm.hasFDerivAt)
  rw [hφx.hasDerivAt.deriv] at hne
  rw [det_fin_one]
  simpa [he] using hne
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicJacobianNeZero
