-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T05:29:47.080916+00:00
-- url     : https://prove2.me/submissions/b355cd88-67fe-4403-aacc-a928d67381c5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleSectionFormsTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PProjIdealFormValue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_ne_zero_3d786f1b7a55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_flag_dual_994e26043ce7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_homog_dd52a81db65b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_chartMono_41728db91770
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartMono_homog_e29ba7e91ef2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_add_24c459fd04ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_chartMono_b9f77329372f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_exists_flag_dual_ed946381b07c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7


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
theorem _root_.solution (y : (Σ k, ι k) → Ω) (B : ChartBundle F (segreVec y) N E)
    (w : Module.Basis (Fin N) Ω E) (b : Fin N → K → ℤ) (hfl : IsFlagFrame y B w b) (a : K → ℤ)
    (φ : Fin M → Module.Dual Ω E) (hφ : IsTwistedDualGens y B a φ) (t : Fin N → Φ) (i : Fin N)
    (c : ∀ k, ι k) (hsc : segreVec y c ≠ 0) :
    ∃ (dl : Option K → ℕ) (β : K → ℕ) (f : MRing (bundleIdx ι M) F), IsMultiHomog f dl ∧
      (fun o => (dl o : ℤ) - liftNat β o) = zetaDeg + liftDeg (b i - a) ∧
      eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f =
        t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
          (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  obtain ⟨ψ, hψint, hψlow, hψi⟩ := exists_flag_dual y B w b hfl c hsc i
  obtain ⟨u, hu, hψ⟩ := hφ.generate c hsc ψ hψint
  have hstar : t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ =
      ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
        projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ := by
    have h1 : ∑ j, truncCoord t ((i : ℕ) + 1) j * algebraMap Ω Φ (ψ (w j)) =
        t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ := by
      rw [Finset.sum_eq_single i]
      · simp [truncCoord, hψi]
      · intro j _ hji
        rcases lt_or_gt_of_ne hji with h | h
        · simp [hψlow j h]
        · have : ¬ (j : ℕ) < (i : ℕ) + 1 := by
            have : (i : ℕ) < j := h
            omega
          simp [truncCoord, this]
      · simp
    rw [← h1, hψ]
    simp only [projCoord, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    simp only [chartPow, Pi.neg_apply]
    ring
  obtain ⟨n, U, hUh, hUe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hu
  let α : K → ℕ := fun k => (|a k| + |b i k| - a k).toNat
  let β : K → ℕ := fun k => (|a k| + |b i k| + n - b i k).toNat
  have hid : segreVec y c ^ n * ∏ k, y ⟨k, c k⟩ ^ α k =
      (∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i) * chartPow y c (-a) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_add hY, ← chartPow_add hY,
      ← chartPow_add hY]
    congr 1
    funext k
    have h1 := le_abs_self (a k)
    have h2 := neg_abs_le (a k)
    have h3 := le_abs_self (b i k)
    have h4 := neg_abs_le (b i k)
    simp only [Pi.add_apply, Pi.neg_apply, α, β]
    omega
  let f : MRing (bundleIdx ι M) F := ∑ l, U l * chartMono M c α * X ⟨none, l⟩
  have hg : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1)))
      (chartMono M c β) = algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := eval_chartMono y w φ _ c β
  have hf : eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω)) (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) f
      = t i * eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
        (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (chartMono M c β) := by
    rw [hg]
    calc _ = ∑ l, algebraMap Ω Φ (u l * chartPow y c (-a)) *
            projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          simp only [f, eval₂_sum, eval₂_mul, eval₂_X, hUe, eval_chartMono]
          refine Finset.sum_congr rfl fun l _ => ?_
          have hl : algebraMap Ω Φ (u l * segreVec y c ^ n) * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ α k) =
              algebraMap Ω Φ (u l * chartPow y c (-a)) *
                algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
            rw [← map_mul, ← map_mul]
            congr 1
            rw [mul_assoc, hid]
            ring
          rw [mul_comm _ (projCoord _ _ _ _ _), mul_assoc, hl]
          ring
      _ = t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ *
            algebraMap Ω Φ ((∏ k, y ⟨k, c k⟩ ^ β k) * chartPow y c (b i)) := by
          rw [hstar, Finset.sum_mul]
      _ = t i * algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ β k) := by
          have hp : algebraMap Ω Φ (chartPow y c (b i)) ≠ 0 :=
            (map_ne_zero _).2 (chartPow_ne_zero hY _)
          rw [map_inv₀, map_mul]
          field_simp
  refine ⟨fun o => Option.elim o 1 (fun k => n + α k), β, f, ?_, ?_, hf⟩
  · refine IsWeightedHomogeneous.sum _ _ _ fun l _ => ?_
    have h := ((hUh l).mul (chartMono_homog (F := F) M c α)).mul
      (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
    convert h using 1
    funext o
    cases o <;> simp [liftNat, blockWeight]
  · funext o
    cases o with
    | none => simp [liftNat, zetaDeg, liftDeg]
    | some k =>
      have h1 := le_abs_self (a k)
      have h2 := neg_abs_le (a k)
      have h3 := le_abs_self (b i k)
      have h4 := neg_abs_le (b i k)
      simp only [liftNat, zetaDeg, liftDeg, Option.elim, Pi.add_apply, Pi.sub_apply, α, β]
      omega
end GroundTheory.Heights₂.Heights.NumbersDVR.FlagBundleChartSection
