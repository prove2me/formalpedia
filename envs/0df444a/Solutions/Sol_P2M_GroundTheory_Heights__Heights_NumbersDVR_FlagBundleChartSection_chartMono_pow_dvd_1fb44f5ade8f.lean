-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:38:24.819403+00:00
-- url     : https://prove2.me/submissions/99e0497a-bff8-4f7e-94bf-09685a42ce79

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
theorem _root_.solution (c : ∀ k, ι k) (δ : K → ℕ) (D : ℕ) :
    chartMono (F := F) M c δ ^ D ∣
      (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ (D * ∑ k, δ k) := by
  rw [chartMono, ← Finset.prod_pow, ← Finset.prod_pow]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun k _ => ?_
  rw [← pow_mul]
  refine pow_dvd_pow _ ?_
  calc δ k * D = D * δ k := Nat.mul_comm _ _
    _ ≤ D * ∑ k, δ k := Nat.mul_le_mul_left D (Finset.single_le_sum (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ k))
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
