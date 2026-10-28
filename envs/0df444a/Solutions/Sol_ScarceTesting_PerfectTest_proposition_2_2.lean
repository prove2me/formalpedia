-- Prove2me | solution 2 for ScarceTesting.PerfectTest.proposition_2
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-27T08:26:41.818055+00:00
-- url     : https://prove2.me/submissions/a70e4fd6-2a4f-4eaf-b557-df05b1b44746

import Mathlib
import Definitions.Def_ScarceTesting_PerfectTest_Setting
import Theorems.Thm_ScarceTesting_PerfectTest_dS_dphi
import Theorems.Thm_ScarceTesting_PerfectTest_dS_dsigma

-- carved verbatim out of submission 6e62e0db-09b8-483c-b041-ee7f50467ec5, lines 731-745

section
set_option autoImplicit false
open MeasureTheory Set Topology ScarceTesting.PerfectTest

lemma hsub (f : ℝ → ℝ) (hf : IsPriorDensity f) (a b : ℝ) (ha : a ∈ Icc (0:ℝ) 1)
    (hb : b ∈ Icc (0:ℝ) 1) : IntervalIntegrable f volume a b := by
  refine hf.integrable.mono_set ?_
  rw [uIcc_of_le zero_le_one]
  exact uIcc_subset_Icc ha hb

lemma wint (f : ℝ → ℝ) (hf : IsPriorDensity f) (w : ℝ → ℝ) (hw : Continuous w) (a b : ℝ)
    (ha : a ∈ Icc (0:ℝ) 1) (hb : b ∈ Icc (0:ℝ) 1) :
    IntervalIntegrable (fun x => w x * f x) volume a b :=
  (hsub f hf a b ha hb).continuousOn_mul hw.continuousOn

lemma wM (f : ℝ → ℝ) (hf : IsPriorDensity f) : ∀ a b : ℝ, a ∈ Icc (0:ℝ) 1 → b ∈ Icc (0:ℝ) 1 →
    IntervalIntegrable (fun μ => μ * f μ) volume a b :=
  fun a b ha hb => wint f hf (fun x => x) continuous_id a b ha hb

lemma wpos (f w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b) (hf : IntervalIntegrable f volume a b)
    (hw : Continuous w) (hf0 : ∀ x ∈ Ioo a b, 0 ≤ f x) (hw0 : ∀ x ∈ Ioo a b, 0 < w x)
    (hint : 0 < ∫ x in a..b, f x) : 0 < ∫ x in a..b, w x * f x := by
  have hfi : IntegrableOn f (Ioo a b) volume := by
    have := (intervalIntegrable_iff_integrableOn_Ioo_of_le hab).1 hf
    exact this
  have hwfi : IntegrableOn (fun x => w x * f x) (Ioo a b) volume := by
    have h1 : IntegrableOn f (Icc a b) volume := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab] at hf
      exact hf
    have : IntegrableOn (fun x => w x * f x) (Icc a b) volume :=
      h1.continuousOn_mul hw.continuousOn isCompact_Icc
    exact this.mono_set Ioo_subset_Icc_self
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hint ⊢
  have hnn : 0 ≤ ∫ x in Ioo a b, w x * f x :=
    setIntegral_nonneg measurableSet_Ioo (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))
  rcases hnn.lt_or_eq with h | h
  · exact h
  exfalso
  have hae : (fun x => w x * f x) =ᵐ[volume.restrict (Ioo a b)] 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae
      ((ae_restrict_iff' measurableSet_Ioo).2 (Filter.Eventually.of_forall
        (fun x hx => (mul_nonneg (hw0 x hx).le (hf0 x hx)))) ) hwfi).1 h.symm
    exact this
  have hf_ae : f =ᵐ[volume.restrict (Ioo a b)] 0 := by
    filter_upwards [hae, ae_restrict_mem measurableSet_Ioo] with x hx hxm
    have := (hw0 x hxm).ne'
    simpa [this] using hx
  have : ∫ x in Ioo a b, f x = 0 := integral_eq_zero_of_ae hf_ae
  linarith

lemma dgp (f : ℝ → ℝ) (c : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hf : IsPriorDensity f) (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c := by
  have hi := hf.integrable
  have hi0c : IntervalIntegrable f volume 0 c :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc0.le]; exact Icc_subset_Icc le_rfl hc1.le)
  have hic1 : IntervalIntegrable f volume c 1 :=
    hi.mono_set (by rw [uIcc_of_le zero_le_one, uIcc_of_le hc1.le]; exact Icc_subset_Icc hc0.le le_rfl)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hi0c hic1
  rw [hf.total] at hsum
  have hnn : ∀ x ∈ Ioo (0:ℝ) 1, 0 ≤ f x := fun x hx => hf.nonneg x (Ioo_subset_Icc_self hx)
  constructor
  · apply wpos f (fun x => 1 - x) c 1 hc1.le hic1 (by fun_prop)
    · intro x hx; exact hnn x ⟨hc0.trans hx.1, hx.2⟩
    · intro x hx; linarith [hx.2]
    · have : cdf f c = ∫ t in (0:ℝ)..c, f t := rfl
      linarith
  · apply wpos f (fun x => x) 0 c hc0.le hi0c (by fun_prop)
    · intro x hx; exact hnn x ⟨hx.1, hx.2.trans hc1⟩
    · intro x hx; exact hx.1
    · exact hFc0

lemma exists_gt_right (g : ℝ → ℝ) (D : ℝ) (hD : 0 < D) (hg : HasDerivWithinAt g D (Ici 0) 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ g 0 < g φ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Ici_sdiff_left] at hg
  have h1 := hg.eventually (lt_mem_nhds hD)
  have h2 : ∀ᶠ φ in 𝓝[>] (0:ℝ), φ < 1 := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  have h3 : ∀ᶠ φ in 𝓝[>] (0:ℝ), 0 < φ := self_mem_nhdsWithin
  obtain ⟨φ, a, b, c⟩ := (h1.and (h2.and h3)).exists
  refine ⟨φ, c, b, ?_⟩
  have h : 0 < slope g 0 φ := a
  rw [slope_def_field] at h
  have h4 : 0 < φ - 0 := by linarith
  have := (div_pos_iff_of_pos_right h4).1 h
  linarith

lemma exists_gt_left (g : ℝ → ℝ) (D : ℝ) (hD : D < 0) (hg : HasDerivWithinAt g D (Iic 1) 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ g 1 < g σ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Iic_sdiff_right] at hg
  have h1 := hg.eventually (gt_mem_nhds hD)
  have h2 : ∀ᶠ σ in 𝓝[<] (1:ℝ), 0 < σ := mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
  have h3 : ∀ᶠ σ in 𝓝[<] (1:ℝ), σ < 1 := self_mem_nhdsWithin
  obtain ⟨σ, a, b, c⟩ := (h1.and (h2.and h3)).exists
  refine ⟨σ, b, c, ?_⟩
  have h : slope g 1 σ < 0 := a
  rw [slope_def_field] at h
  have h4 : σ - 1 < 0 := by linarith
  by_contra hcon
  push_neg at hcon
  have : 0 ≤ (g σ - g 1) / (σ - 1) := div_nonneg_of_nonpos (by linarith) h4.le
  linarith

lemma mean_eq (f : ℝ → ℝ) (hf : IsPriorDensity f) :
    ∫ μ in (0:ℝ)..1, (1 - μ) * f μ = 1 - meanPrior f := by
  have h : (fun μ => (1 - μ) * f μ) = fun μ => f μ - μ * f μ := by funext μ; ring
  rw [h, intervalIntegral.integral_sub hf.integrable (wM f hf 0 1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩), hf.total]
  rfl

lemma prop_i (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0) :
    ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1 := by
  obtain ⟨hδ, hγ⟩ := dgp f c hc0 hc1 hf hFc0 hFc1
  have hY : 0 < β * deltaC f c + gammaC f c := by
    have := mul_nonneg hβ0 hδ.le
    linarith
  have hd := ScarceTesting.PerfectTest.dS_dphi f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf0
  have h1c : 0 < 1 - c := by linarith
  rw [mean_eq f hf] at hd
  have key : β * (1 - meanPrior f) * ((1 - c) / c) < f 0 * (β * deltaC f c + gammaC f c) := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hY] at h
    exact h
  have hD : 0 < -κ * β * (1 - meanPrior f) +
      c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ) := by
    have e : -κ * β * (1 - meanPrior f) +
      c / (1 - c) * κ * f 0 * (β * (∫ μ in c..1, (1 - μ) * f μ) + ∫ μ in (0:ℝ)..c, μ * f μ) =
        κ * (c / (1 - c)) * (f 0 * (β * deltaC f c + gammaC f c) -
          β * (1 - meanPrior f) * ((1 - c) / c)) := by
      unfold deltaC gammaC
      field_simp
      ring
    rw [e]
    have : 0 < f 0 * (β * deltaC f c + gammaC f c) - β * (1 - meanPrior f) * ((1 - c) / c) := by
      linarith
    positivity
  exact exists_gt_right _ _ hD hd

lemma prop_ii (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1)
    (h : c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) < f 1) :
    ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ S f c β κ 0 1 < S f c β κ 0 σ := by
  obtain ⟨hδ, hγ⟩ := dgp f c hc0 hc1 hf hFc0 hFc1
  have hY : 0 < β * deltaC f c + gammaC f c := by
    have := mul_nonneg hβ0 hδ.le
    linarith
  have hd := ScarceTesting.PerfectTest.dS_dsigma f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf1
  have h1c : 0 < 1 - c := by linarith
  have key : c * meanPrior f < f 1 * ((1 - c) * (β * deltaC f c + gammaC f c)) := by
    have e : c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) =
        c * meanPrior f / ((1 - c) * (β * deltaC f c + gammaC f c)) := by
      field_simp
    rw [e, div_lt_iff₀ (mul_pos h1c hY)] at h
    exact h
  have hD : -κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ) < 0 := by
    have e : -κ * f 1 * ((1 - c) / c) * β * (∫ μ in c..1, (1 - μ) * f μ) +
        κ * (∫ μ in (0:ℝ)..1, μ * f μ) -
        κ * f 1 * ((1 - c) / c) * (∫ μ in (0:ℝ)..c, μ * f μ) =
        κ / c * (c * meanPrior f - f 1 * ((1 - c) * (β * deltaC f c + gammaC f c))) := by
      unfold deltaC gammaC meanPrior
      field_simp
      ring
    rw [e]
    have : c * meanPrior f - f 1 * ((1 - c) * (β * deltaC f c + gammaC f c)) < 0 := by linarith
    exact mul_neg_of_pos_of_neg (by positivity) this
  exact exists_gt_left _ _ hD hd

theorem solution (f : ℝ → ℝ) (c β κ : ℝ) (hc0 : 0 < c) (hc1 : c < 1)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hf : IsPriorDensity f)
    (hf0 : ContinuousWithinAt f (Set.Icc 0 1) 0) (hf1 : ContinuousWithinAt f (Set.Icc 0 1) 1)
    (hFc0 : 0 < cdf f c) (hFc1 : cdf f c < 1) :
    0 < deltaC f c ∧ 0 < gammaC f c ∧
    (β * (1 - meanPrior f) / (β * deltaC f c + gammaC f c) * ((1 - c) / c) < f 0 →
      ∃ φ : ℝ, 0 < φ ∧ φ < 1 ∧ S f c β κ 0 1 < S f c β κ φ 1) ∧
    (c / (1 - c) * (meanPrior f / (β * deltaC f c + gammaC f c)) < f 1 →
      ∃ σ : ℝ, 0 < σ ∧ σ < 1 ∧ S f c β κ 0 1 < S f c β κ 0 σ) := by
  obtain ⟨hδ, hγ⟩ := dgp f c hc0 hc1 hf hFc0 hFc1
  exact ⟨hδ, hγ,
    fun h => prop_i f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf0 hFc0 hFc1 h,
    fun h => prop_ii f c β κ hc0 hc1 hβ0 hβ1 hκ0 hκ1 hf hf1 hFc0 hFc1 h⟩

end
