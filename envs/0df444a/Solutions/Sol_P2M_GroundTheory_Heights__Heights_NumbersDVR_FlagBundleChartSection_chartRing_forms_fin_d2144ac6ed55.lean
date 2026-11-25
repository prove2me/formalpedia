-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:23:11.780261+00:00
-- url     : https://prove2.me/submissions/f74f9288-e002-4191-9c35-0ad184a09fba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_homog_dd52a81db65b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_chartMono_41728db91770
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_4fe7616a415d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartMono_homog_e29ba7e91ef2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartRing_forms_a08c172c2f9a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_chartMono_b9f77329372f


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
    (φ : Fin M → Module.Dual Ω E) (t : Fin N → Φ) (c : ∀ k, ι k) (hc : segreVec y c ≠ 0) {L : ℕ}
    {u : Fin L → Ω} (hu : ∀ l, u l ∈ chartRing F (segreVec y) c) :
    ∃ (n : ℕ) (U : Fin L → MRing (bundleIdx ι M) F), (∀ l, IsMultiHomog (U l) (liftNat fun _ => n)) ∧
      ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ t) (U l) =
        algebraMap Ω Φ (u l * segreVec y c ^ n) := by
  have h := fun l => chartRing_forms (M := M) y w φ t c hc (hu l)
  choose n U hU hUe using h
  refine ⟨∑ l, n l, fun l => U l * chartMono M c (fun _ => ∑ l, n l - n l), fun l => ?_, fun l => ?_⟩
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    have hd : liftNat (K := K) (fun _ => ∑ l, n l) =
        liftNat (fun _ => n l) + liftNat (fun _ => ∑ l, n l - n l) := by
      funext o; cases o <;> simp [liftNat]; omega
    rw [hd]
    exact (hU l).mul (chartMono_homog M c _)
  · have hle : n l ≤ ∑ l, n l := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
    rw [eval₂_mul, hUe, eval_chartMono, ← map_mul]
    congr 1
    rw [Finset.prod_pow, mul_assoc, ← segreVec, ← pow_add, Nat.add_sub_cancel' hle]
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
