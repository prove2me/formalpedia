-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:39:04.279469+00:00
-- url     : https://prove2.me/submissions/244206a7-d576-47e4-b52e-f8e6413d6f61

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
theorem _root_.solution (u : MRing (bundleIdx ι M) F) {q : MRing (bundleIdx ι M) F} {d : Option K → ℕ}
    (hq : IsMultiHomog q d) :
    bind₁ (fun v => u ^ blockWeight (bundleIdx ι M) v none * X v) q = u ^ d none * q := by
  conv_lhs => rw [← q.support_sum_monomial_coeff]
  conv_rhs => rw [← q.support_sum_monomial_coeff]
  rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hmd : Finsupp.weight (blockWeight (bundleIdx ι M)) m = d := hq (mem_support_iff.mp hm)
  have hs : ∑ v ∈ m.support, blockWeight (bundleIdx ι M) v none * m v = d none := by
    rw [← hmd, Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun v _ => ?_
    simp [mul_comm]
  rw [bind₁_monomial, monomial_eq, Finsupp.prod]
  simp only [mul_pow, Finset.prod_mul_distrib, ← pow_mul]
  rw [Finset.prod_pow_eq_pow_sum, hs]
  ring
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
