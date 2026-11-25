-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:29.43473+00:00
-- url     : https://prove2.me/submissions/2d9df648-bfe1-4b81-9c40-4eea811936e2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_eval__monomial_cone_2bc04389d40a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_proof_793669600b5a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_weight_blockWeight_apply_e50de9fe3a17


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
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) {q : MRing (bundleIdx ι M) F}
    (hq : q ∈ projIdeal F y w φ t) (d : Option K → ℕ) :
    weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈ projIdeal F y w φ t := by
  classical
  rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ t d _
    (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [projIdeal, RingHom.mem_ker, coe_eval₂Hom] at hq
  have hc := congrArg (coeff (Finsupp.equivFunOnFinite.symm d)) hq
  rw [← q.support_sum_monomial_coeff, eval₂_sum, coeff_sum, coeff_zero] at hc
  rw [weightedHomogeneousComponent_apply, eval₂_sum, Finset.sum_filter]
  refine (Finset.sum_congr rfl fun m _ => ?_).trans hc
  rw [ProjIdealFormValue.eval₂_monomial_cone, coeff_C_mul, coeff_monomial, mul_ite, mul_one, mul_zero]
  have hiff : Finsupp.mapDomain Sigma.fst m = Finsupp.equivFunOnFinite.symm d ↔
      Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := by
    rw [Finsupp.ext_iff, funext_iff]
    exact forall_congr' fun o => by rw [ProjIdealFormValue.weight_blockWeight_apply]; rfl
  simp only [hiff]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
