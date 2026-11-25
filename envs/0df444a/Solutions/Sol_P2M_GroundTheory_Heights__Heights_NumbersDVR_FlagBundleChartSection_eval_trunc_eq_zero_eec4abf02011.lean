-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:23:05.192275+00:00
-- url     : https://prove2.me/submissions/e5e30e6f-0d75-477e-b10f-34cdbf0e3086

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_eq_zero_of_mem_projIdeal_77c3761ef824


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
set_option linter.unusedSectionVars false
open GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
open FlagBundleSectionForms (chartPow chartMono liftNat)
variable {F : Type} [Field F] {Ω : Type} [Field Ω] [Algebra F Ω]
  {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type}
variable {M N : ℕ} {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ] [Algebra Ω Φ]
namespace GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
theorem _root_.solution (y : (Σ k, ι k) → Ω) (w : Module.Basis (Fin N) Ω E)
    (φ : Fin M → Module.Dual Ω E) {t : Fin N → Φ} (ht : AlgebraicIndependent Ω t) (i : ℕ)
    {q : MRing (bundleIdx ι M) F} (hq : q ∈ projIdeal F y w φ (truncCoord t i)) (τ : Fin N → Φ) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord τ i)) q = 0 := by
  classical
  let G : (Σ o, bundleIdx ι M o) → MvPolynomial (Fin N) Ω := fun p =>
    match p with
    | ⟨none, l⟩ => ∑ j : Fin N, (if (j : ℕ) < i then X j else 0) * C (φ l (w j))
    | ⟨some k, p⟩ => C (y ⟨k, p⟩)
  have key : ∀ τ : Fin N → Φ, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord τ i)) q =
      aeval τ (eval₂ (C.comp (algebraMap F Ω)) G q) := by
    intro τ
    have h := eval₂_comp_left (aeval τ : MvPolynomial (Fin N) Ω →ₐ[Ω] Φ).toRingHom
      (C.comp (algebraMap F Ω)) G q
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
    rw [h]
    congr 1
    · ext r
      simp
    · funext p
      rcases p with ⟨_ | k, p⟩
      · simp [G, projCoord, truncCoord, map_sum, apply_ite]
      · simp [G, projCoord]
  have h0 : eval₂ (C.comp (algebraMap F Ω)) G q = 0 :=
    ht (by rw [map_zero, ← key t]; exact eval_eq_zero_of_mem_projIdeal y w φ _ hq)
  rw [key τ, h0, map_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
