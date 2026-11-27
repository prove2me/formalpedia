-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_proof_d02a86799748
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:04:53.394488+00:00
-- url     : https://prove2.me/submissions/c041ccde-275b-4212-9378-c5bf30d883ba

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsFlagBundleChartSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSectionTools
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PFlagBundleChartSection
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__isMultiHomog_6dc8a1e2712d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__scale_807f029d6562
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_bind__sub_mem_1ef7404e28f6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_homog_dd52a81db65b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartMono_pow_dvd_1fb44f5ade8f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_add_06212d674b74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_natCast_95b9d4002130
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartPow_ne_zero_3d786f1b7a55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_chartRing_forms_fin_d2144ac6ed55
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_component_mem_projIdeal_cedf5a28dfa6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_chartMono_41728db91770
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_eval_trunc_eq_zero_eec4abf02011
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_exists_section_form_0be7fabf5a7b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_isMultiHomog_sub_f3f3a0c7d185
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleChartSection_segreVec_pow_597b9ec89db6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartMono_homog_e29ba7e91ef2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_add_24c459fd04ad
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_natCast_864f6fcab797
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_chartPow_ne_zero_53c4f1e3f5a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_eval_chartMono_b9f77329372f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_FlagBundleSectionForms_segreVec_pow_851cfbba86d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_ProjIdealFormValue_proof_793669600b5a


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
open FlagBundleSectionForms (chartPow chartMono liftNat)
open FlagBundleChartSection
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace FlagBundleChartSection
theorem _root_.solution : FlagBundleChartSection.Statement := by
  intro F _ Ω _ _ K _ _ ι y N E _ _ B w b hfl M a φ hφ Φ _ _ t ht i c hsc
  classical
  have hY : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (Finset.prod_ne_zero_iff.1 hsc) k (Finset.mem_univ _)
  have hcpb : chartPow y c (b i) ≠ 0 := chartPow_ne_zero hY _
  obtain ⟨dl, β, f, hfh, hdeg, hfv⟩ := exists_section_form (M := M) y B w b hfl a φ hφ t i c hsc

  obtain ⟨vi, hviL, hviT, hviD⟩ : ∃ v ∈ B.lat c, (∀ j, i < j → w.repr v j = 0) ∧
      w.repr v i = chartPow y c (b i) := by
    have h := hfl.graded c hsc i
    rw [Set.ext_iff] at h
    exact (h (chartPow y c (b i))).2 ⟨1, one_mem _, (one_mul _).symm⟩

  have hr : ∀ l, ∃ r ∈ chartRing F (segreVec y) c, φ l vi = r * chartPow y c a :=
    fun l => hφ.sections c hsc l vi hviL
  choose r hrA hrv using hr
  obtain ⟨n₂, R, hRh, hRe⟩ := chartRing_forms_fin (M := M) y w φ (truncCoord t ((i : ℕ) + 1)) c hsc hrA

  let γ₁ : K → ℕ := fun k => (b i k - a k).toNat
  let γ₂ : K → ℕ := fun k => (a k - b i k).toNat
  let δ : K → ℕ := β + fun k => n₂ + γ₁ k
  let u : MRing (bundleIdx ι M) F := chartMono M c δ
  let Y : Fin M → MRing (bundleIdx ι M) F := fun l => u * X ⟨none, l⟩ - R l * chartMono M c γ₂ * f
  let g : (Σ o, bundleIdx ι M o) → MRing (bundleIdx ι M) F := fun v =>
    match v with
    | ⟨none, l⟩ => Y l
    | ⟨some k, p⟩ => X ⟨some k, p⟩
  let e : Option K → ℕ := fun o => liftNat δ o + Option.elim o 1 (fun _ => 0)
  have hYh : ∀ l, IsMultiHomog (Y l) e := by
    intro l
    refine isMultiHomog_sub ?_ ?_
    · have h := (chartMono_homog (F := F) M c δ).mul
        (isWeightedHomogeneous_X F (blockWeight (bundleIdx ι M)) ⟨none, l⟩)
      have he : e = liftNat δ + blockWeight (bundleIdx ι M) ⟨none, l⟩ := by
        funext o
        cases o <;> simp [e, liftNat, blockWeight]
      rw [he]
      exact h
    · have h := ((hRh l).mul (chartMono_homog (F := F) M c γ₂)).mul hfh
      have he : e = (liftNat fun _ => n₂) + liftNat γ₂ + dl := by
        funext o
        cases o with
        | none =>
          have h0 := congrFun hdeg none
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat]
          omega
        | some k =>
          have h0 := congrFun hdeg (some k)
          simp [liftNat, zetaDeg, liftDeg] at h0
          simp [e, liftNat, δ, γ₁, γ₂]
          omega
      rw [he]
      exact h
  have hid : (∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a =
      (∏ k, y ⟨k, c k⟩ ^ β k) * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * chartPow y c (b i) := by
    rw [segreVec_pow, ← chartPow_natCast, ← chartPow_natCast, ← chartPow_natCast]
    simp only [← chartPow_add hY]
    congr 1
    funext k
    simp only [Pi.add_apply, δ, γ₁, γ₂]
    omega
  have hevY : ∀ l, eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (Y l) =
      algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * projCoord y w φ (truncCoord t ((i : ℕ) + 1)) ⟨none, l⟩ -
        algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * (t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹) *
          algebraMap Ω Φ (φ l vi) := by
    intro l
    have hΩ : r l * segreVec y c ^ n₂ * (∏ k, y ⟨k, c k⟩ ^ γ₂ k) * (∏ k, y ⟨k, c k⟩ ^ β k) =
        (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) := by
      rw [show (∏ k, y ⟨k, c k⟩ ^ δ k) * (chartPow y c (b i))⁻¹ * (r l * chartPow y c a) =
        r l * ((∏ k, y ⟨k, c k⟩ ^ δ k) * chartPow y c a) * (chartPow y c (b i))⁻¹ by ring, hid]
      field_simp
    have h2 := congrArg (algebraMap Ω Φ) hΩ
    simp only [Y, u, eval₂_sub, eval₂_mul, eval₂_X, hRe, eval_chartMono, hfv, hrv]
    simp only [map_mul, map_inv₀] at h2 ⊢
    linear_combination (-(t i)) * h2

  have hgev : (fun v => eval₂ ((algebraMap Ω Φ).comp (algebraMap F Ω))
      (projCoord y w φ (truncCoord t ((i : ℕ) + 1))) (g v)) =
      projCoord y w φ (truncCoord (fun j => algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) *
        (t j - t i * algebraMap Ω Φ (chartPow y c (b i))⁻¹ * algebraMap Ω Φ (w.repr vi j))) i) := by
    funext v
    rcases v with ⟨_ | k, p⟩
    · show eval₂ _ _ (Y p) = _
      have hφv : algebraMap Ω Φ (φ p vi) =
          ∑ j, algebraMap Ω Φ (w.repr vi j) * algebraMap Ω Φ (φ p (w j)) := by
        conv_lhs => rw [← w.sum_repr vi]
        simp only [map_sum, map_smul, smul_eq_mul, map_mul]
      rw [hevY p, hφv]
      simp only [projCoord]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [truncCoord]
      rcases lt_trichotomy j i with h | h | h
      · have h1 : (j : ℕ) < i := h
        have h2 : (j : ℕ) < (i : ℕ) + 1 := by omega
        simp only [h1, h2, if_true]
        ring
      · subst h
        have h1 : ¬ (j : ℕ) < j := lt_irrefl _
        have h2 : (j : ℕ) < (j : ℕ) + 1 := Nat.lt_succ_self _
        have hσ : t j * algebraMap Ω Φ (chartPow y c (b j))⁻¹ * algebraMap Ω Φ (chartPow y c (b j)) = t j := by
          rw [mul_assoc, ← map_mul, inv_mul_cancel₀ hcpb, map_one, mul_one]
        simp only [h1, h2, if_true, if_false, hviD]
        linear_combination (-(algebraMap Ω Φ (∏ k, y ⟨k, c k⟩ ^ δ k) * algebraMap Ω Φ (φ p (w j)))) * hσ
      · have h1 : ¬ (j : ℕ) < i := by
          have : (i : ℕ) < j := h
          omega
        have h2 : ¬ (j : ℕ) < (i : ℕ) + 1 := by
          have : (i : ℕ) < j := h
          omega
        simp only [h1, h2, if_false, hviT j h, map_zero]
        ring
    · rw [eval₂_X]
      rfl

  have hform : ∀ (d : Option K → ℕ) (q : MRing (bundleIdx ι M) F), IsMultiHomog q d →
      q ∈ projIdeal F y w φ (truncCoord t i) →
      u ^ d none * q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d q hq hqI
    have h1 : bind₁ g q ∈ projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) := by
      rw [ProjIdealFormValue.proof F Ω K ι y N E w M φ Φ _ _ _
        (bind₁_isMultiHomog g e (fun _ _ => rfl) hYh hq)]
      rw [← coe_eval₂Hom, eval₂Hom_bind₁, coe_eval₂Hom]
      simp only [coe_eval₂Hom]
      rw [hgev]
      exact eval_trunc_eq_zero y w φ ht i hqI _
    have h2 : u ^ d none * q - bind₁ g q ∈ Ideal.span {f} := by
      rw [← bind₁_scale u hq]
      refine bind₁_sub_mem _ g _ (fun v => ?_) q
      rcases v with ⟨_ | k, p⟩
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨none, p⟩ none * X ⟨none, p⟩ - g ⟨none, p⟩ =
            R p * chartMono M c γ₂ * f := by
          simp [g, Y, blockWeight]
        rw [h3]
        exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self f)
      · have h3 : u ^ blockWeight (bundleIdx ι M) ⟨some k, p⟩ none * X ⟨some k, p⟩ - g ⟨some k, p⟩ = 0 := by
          simp [g, blockWeight]
        rw [h3]
        exact zero_mem _
    have h3 : bind₁ g q + (u ^ d none * q - bind₁ g q) ∈
        projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} :=
      Ideal.add_mem _ (Ideal.mem_sup_left h1) (Ideal.mem_sup_right h2)
    rwa [add_sub_cancel] at h3
  refine ⟨dl, liftNat β, f, chartMono M c β, β, rfl, hfh, chartMono_homog M c β, hdeg, hfv, ?_⟩
  intro q hq

  have hsat : ∀ d, ∃ n : ℕ, (∏ k, (X ⟨some k, c k⟩ : MRing (bundleIdx ι M) F)) ^ n *
      weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q ∈
      projIdeal F y w φ (truncCoord t ((i : ℕ) + 1)) ⊔ Ideal.span {f} := by
    intro d
    have hqd := hform d _ (weightedHomogeneousComponent_isWeightedHomogeneous _ _)
      (component_mem_projIdeal y w φ _ hq d)
    obtain ⟨r', hr'⟩ := chartMono_pow_dvd (F := F) (M := M) c δ (d none)
    refine ⟨d none * ∑ k, δ k, ?_⟩
    rw [hr', mul_comm (chartMono M c δ ^ d none) r', mul_assoc]
    exact Ideal.mul_mem_left _ _ hqd
  choose nn hnn using hsat
  obtain ⟨S, hS⟩ : ∃ S : Finset (Option K → ℕ),
      q = ∑ d ∈ S, weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) d q := by
    have hfin := weightedHomogeneousComponent_finsupp (w := blockWeight (bundleIdx ι M)) q
    refine ⟨hfin.toFinset, ?_⟩
    conv_lhs => rw [← sum_weightedHomogeneousComponent (blockWeight (bundleIdx ι M)) q]
    exact finsum_eq_sum _ hfin
  refine ⟨∑ d ∈ S, nn d, ?_⟩
  rw [hS, Finset.mul_sum]
  refine Ideal.sum_mem _ fun d hd => ?_
  rw [← Nat.sub_add_cancel (Finset.single_le_sum (f := nn) (fun _ _ => Nat.zero_le _) hd), pow_add,
    mul_assoc]
  exact Ideal.mul_mem_left _ _ (hnn d)
end FlagBundleChartSection
end GroundTheory.Heights₂.Heights.NumbersDVR
