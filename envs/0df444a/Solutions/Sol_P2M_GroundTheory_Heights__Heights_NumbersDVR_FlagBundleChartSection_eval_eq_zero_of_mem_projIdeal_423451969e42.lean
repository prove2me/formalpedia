-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_eq_zero_of_mem_projIdeal_423451969e42
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:30.667626+00:00
-- url     : https://prove2.me/submissions/7bfbade3-0178-48be-9926-5e7f2e3f9273

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools

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
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {f : MRing (bundleIdx ι M) F}
    (hf : f ∈ projIdeal F y w φ t) :
    eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) f = 0 := by
  have h : (MvPolynomial.eval (fun _ : Option K => (1 : Φ))).comp
      (eval₂Hom (C.comp ((algebraMap Ω Φ).comp (algebraMap F Ω)))
        (fun p => C (projCoord y w φ t p) * X p.1)) =
      eval₂Hom ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp
    · intro p; simp
  rw [projIdeal, RingHom.mem_ker] at hf
  rw [← coe_eval₂Hom, ← h, RingHom.comp_apply, hf, map_zero]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
