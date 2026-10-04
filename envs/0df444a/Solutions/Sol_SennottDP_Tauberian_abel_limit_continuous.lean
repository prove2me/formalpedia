-- Prove2me | solution 1 for SennottDP.Tauberian.abel_limit_continuous
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T17:58:32.983976+00:00
-- url     : https://prove2.me/submissions/a7d8062d-5f62-46df-b3d8-a0985c278725

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Theorems.Thm_SennottDP_Tauberian_abel_limit_monomial

open scoped ENNReal NNReal Topology
open Filter

namespace SennottDP.Tauberian

/-- The real Abel-type mean `(1-α) ∑ α^n u_n g(α^n)`. -/
noncomputable def alcAr (u : ℕ → ℝ≥0∞) (g : ℝ → ℝ) (α : ℝ≥0) : ℝ :=
  (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)

/-- "Good" parameters: `0 < α < 1` and `U(α) < ∞`. -/
def alcGood (u : ℕ → ℝ≥0∞) (α : ℝ≥0) : Prop :=
  0 < α ∧ α < 1 ∧ U u α ≠ ⊤

theorem alcGood_fin {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : alcGood u α) (n : ℕ) : u n ≠ ⊤ := by
  obtain ⟨h0, -, hU⟩ := h
  have hle : (α : ℝ≥0∞) ^ n * u n ≤ U u α := ENNReal.le_tsum (f := fun n => (α : ℝ≥0∞) ^ n * u n) n
  have hne : (α : ℝ≥0∞) ^ n * u n ≠ ⊤ := ne_top_of_le_ne_top hU hle
  intro hu
  apply hne
  rw [hu]
  exact ENNReal.mul_top (pow_ne_zero _ (by exact_mod_cast h0.ne'))

theorem alcGood_summable {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : alcGood u α) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal) := by
  have := ENNReal.summable_toReal h.2.2
  refine this.congr fun n => ?_
  simp [ENNReal.toReal_mul, ENNReal.toReal_pow]

theorem alcGood_tsum {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : alcGood u α) (k : ℕ) :
    (∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ((α : ℝ≥0∞) ^ n) ^ k).toReal =
      ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * ((α : ℝ) ^ n) ^ k := by
  rw [ENNReal.tsum_toReal_eq]
  · refine tsum_congr fun n => ?_
    simp [ENNReal.toReal_mul, ENNReal.toReal_pow]
  · intro n
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top)
      (alcGood_fin h n)) (ENNReal.pow_ne_top (ENNReal.pow_ne_top ENNReal.coe_ne_top))

theorem alcGood_one_sub {α : ℝ≥0} (h : α < 1) : (1 - (α : ℝ≥0∞)).toReal = 1 - (α : ℝ) := by
  rw [ENNReal.toReal_sub_of_le (by exact_mod_cast h.le) ENNReal.one_ne_top]
  simp

theorem alcGood_mem {α : ℝ≥0} (h : α < 1) (n : ℕ) : (α : ℝ) ^ n ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by positivity, pow_le_one₀ (by positivity) (by exact_mod_cast h.le)⟩

theorem alc_summable_of_bound {u : ℕ → ℝ≥0∞} {α : ℝ≥0} (h : alcGood u α) (g : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) :
    Summable (fun n : ℕ => (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)) := by
  refine Summable.of_norm_bounded ((alcGood_summable h).mul_right B) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left (hB _ (alcGood_mem h.2.1 n)) (by positivity)

theorem alc_bound_of_contOn (g : ℝ → ℝ) (hg : ContinuousOn g (Set.Icc 0 1)) :
    ∃ B : ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hg
  exact ⟨B, fun x hx => by simpa [Real.norm_eq_abs] using hB x hx⟩

theorem alc_eventually_good (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), alcGood u α := by
  have h1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), α < 1 := self_mem_nhdsWithin
  have h2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), 0 < α :=
    nhdsWithin_le_nhds (lt_mem_nhds (zero_lt_one : (0 : ℝ≥0) < 1))
  have h3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), abelMean u α < L + 1 :=
    hlim.eventually (gt_mem_nhds (ENNReal.lt_add_right hL one_ne_zero))
  filter_upwards [h1, h2, h3] with α a1 a2 a3
  refine ⟨a2, a1, ?_⟩
  have hα' : (α : ℝ≥0∞) < 1 := by exact_mod_cast a1
  have h0 : (1 - (α : ℝ≥0∞)) ≠ 0 := (tsub_pos_of_lt hα').ne'
  have hfin : abelMean u α ≠ ⊤ := ne_top_of_lt (lt_of_lt_of_le a3 le_top) |>.symm.symm
  · intro hU
    apply (lt_of_lt_of_le a3 le_top).ne
    unfold abelMean
    rw [hU, ENNReal.mul_top h0]

theorem alc_monomial (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (k : ℕ) :
    Tendsto (alcAr u (fun x => x ^ k)) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, x ^ k)) := by
  have hm := abel_limit_monomial u hu0 L hL hlim k
  have hne : L / ((k : ℝ≥0∞) + 1) ≠ ⊤ := ENNReal.div_ne_top hL (by positivity)
  have ht := (ENNReal.tendsto_toReal hne).comp hm
  have hval : (L / ((k : ℝ≥0∞) + 1)).toReal = L.toReal * ∫ x in (0 : ℝ)..1, x ^ k := by
    rw [integral_pow, ENNReal.toReal_div, ENNReal.toReal_add (by simp) (by simp)]
    simp [div_eq_mul_inv]
  rw [hval] at ht
  refine ht.congr' ?_
  filter_upwards [alc_eventually_good u L hL hlim] with α hα
  simp only [Function.comp, alcAr]
  rw [ENNReal.toReal_mul, alcGood_one_sub hα.2.1, alcGood_tsum hα]

theorem alc_one (u : ℕ → ℝ≥0∞) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (alcAr u (fun _ => 1)) (𝓝[<] (1 : ℝ≥0)) (𝓝 L.toReal) := by
  have ht := (ENNReal.tendsto_toReal hL).comp hlim
  refine ht.congr' ?_
  filter_upwards [alc_eventually_good u L hL hlim] with α hα
  simp only [Function.comp, alcAr, abelMean, U]
  rw [ENNReal.toReal_mul, alcGood_one_sub hα.2.1]
  have := alcGood_tsum hα 0
  simp only [pow_zero, mul_one] at this
  rw [this]
  simp

theorem alc_add (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : alcGood u α) (g₁ g₂ : ℝ → ℝ)
    (h₁ : ContinuousOn g₁ (Set.Icc 0 1)) (h₂ : ContinuousOn g₂ (Set.Icc 0 1)) :
    alcAr u (fun x => g₁ x + g₂ x) α = alcAr u g₁ α + alcAr u g₂ α := by
  obtain ⟨B₁, hB₁⟩ := alc_bound_of_contOn g₁ h₁
  obtain ⟨B₂, hB₂⟩ := alc_bound_of_contOn g₂ h₂
  unfold alcAr
  rw [← mul_add, ← (alc_summable_of_bound h g₁ B₁ hB₁).tsum_add
    (alc_summable_of_bound h g₂ B₂ hB₂)]
  congr 1
  exact tsum_congr fun n => by ring

theorem alc_smul (u : ℕ → ℝ≥0∞) (α : ℝ≥0) (g : ℝ → ℝ) (c : ℝ) :
    alcAr u (fun x => c * g x) α = c * alcAr u g α := by
  unfold alcAr
  beta_reduce
  rw [show (∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * (c * g ((α : ℝ) ^ n))) =
      ∑' n : ℕ, c * ((α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)) from
      tsum_congr fun n => by ring, tsum_mul_left]
  ring

theorem alc_poly (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (p : Polynomial ℝ) :
    Tendsto (alcAr u (fun x => p.eval x)) (𝓝[<] (1 : ℝ≥0))
      (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, p.eval x)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    have hint : ∫ x in (0 : ℝ)..1, (p + q).eval x =
        (∫ x in (0 : ℝ)..1, p.eval x) + ∫ x in (0 : ℝ)..1, q.eval x := by
      simp only [Polynomial.eval_add]
      exact intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
        (q.continuous.intervalIntegrable _ _)
    rw [hint, mul_add]
    refine (hp.add hq).congr' ?_
    filter_upwards [alc_eventually_good u L hL hlim] with α hα
    simp only [Polynomial.eval_add]
    exact (alc_add u hα _ _ p.continuous.continuousOn q.continuous.continuousOn).symm
  | monomial n a =>
    simp only [Polynomial.eval_monomial]
    have hm := (alc_monomial u hu0 L hL hlim n).const_mul a
    rw [intervalIntegral.integral_const_mul]
    have : L.toReal * (a * ∫ x in (0 : ℝ)..1, x ^ n) = a * (L.toReal * ∫ x in (0 : ℝ)..1, x ^ n) :=
      by ring
    rw [this]
    refine hm.congr fun α => ?_
    exact (alc_smul u α (fun x => x ^ n) a).symm

theorem alc_abs_le (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : alcGood u α) (g : ℝ → ℝ) (ε : ℝ)
    (hg : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ ε) :
    |alcAr u g α| ≤ ε * alcAr u (fun _ => 1) α := by
  unfold alcAr
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    linarith
  have hs := alc_summable_of_bound h g ε hg
  have hsn : Summable (fun n : ℕ => ‖(α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)‖) := hs.norm
  rw [abs_mul, abs_of_nonneg h1]
  have : |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)| ≤
      ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1 := by
    calc |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)|
        ≤ ∑' n : ℕ, ‖(α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)‖ := by
          rw [← Real.norm_eq_abs]; exact norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' n : ℕ, ε * ((α : ℝ) ^ n * (u n).toReal * 1) := by
          refine hsn.tsum_le_tsum (fun n => ?_) ((alcGood_summable h).mul_left ε |>.congr
            fun n => by ring)
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
          have := hg _ (alcGood_mem h.2.1 n)
          nlinarith [show (0 : ℝ) ≤ (α : ℝ) ^ n * (u n).toReal by positivity]
      _ = ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1 := tsum_mul_left
  calc (1 - (α : ℝ)) * |∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * g ((α : ℝ) ^ n)|
      ≤ (1 - (α : ℝ)) * (ε * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * 1) :=
        mul_le_mul_of_nonneg_left this h1
    _ = _ := by ring

theorem alc_main (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (alcAr u f) (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ℓ := L.toReal
  have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set δ := ε / (4 * (ℓ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 1 f hf δ hδpos
  have hpoly := alc_poly u hu0 L hL hlim p
  have e1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      dist (alcAr u (fun x => p.eval x) α) (ℓ * ∫ x in (0 : ℝ)..1, p.eval x) < ε / 4 :=
    Metric.tendsto_nhds.mp hpoly (ε / 4) (by positivity)
  have e2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), alcAr u (fun _ => 1) α < ℓ + 1 :=
    (alc_one u L hL hlim).eventually (gt_mem_nhds (by linarith))
  set If := ∫ x in (0 : ℝ)..1, f x with hIf
  set Ip := ∫ x in (0 : ℝ)..1, p.eval x with hIp
  have hI : |If - Ip| ≤ δ := by
    rw [hIf, hIp, ← intervalIntegral.integral_sub (hf.intervalIntegrable_of_Icc zero_le_one)
      (p.continuous.intervalIntegrable _ _)]
    have := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 1)
      (f := fun x => f x - p.eval x) (C := δ) (fun x hx => by
        rw [Set.uIoc_of_le zero_le_one] at hx
        rw [Real.norm_eq_abs, abs_sub_comm]
        exact (hp x ⟨hx.1.le, hx.2⟩).le)
    simpa using this
  have hint : |ℓ * If - ℓ * Ip| ≤ ℓ * δ := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hℓ]
    exact mul_le_mul_of_nonneg_left hI hℓ
  filter_upwards [e1, e2, alc_eventually_good u L hL hlim] with α a1 a2 hα
  have hdiff : |alcAr u f α - alcAr u (fun x => p.eval x) α| ≤ δ * alcAr u (fun _ => 1) α := by
    have hsplit := alc_add u hα (fun x => f x - p.eval x) (fun x => p.eval x)
      (hf.sub p.continuous.continuousOn) p.continuous.continuousOn
    simp only [sub_add_cancel] at hsplit
    rw [hsplit, add_sub_cancel_right]
    exact alc_abs_le u hα _ δ fun x hx => by rw [abs_sub_comm]; exact (hp x hx).le
  have hone_nn : 0 ≤ alcAr u (fun _ => 1) α := by
    have := alc_abs_le u hα (fun _ => 0) 0 (by simp)
    have h1 : (0 : ℝ) ≤ 1 - (α : ℝ) := by
      have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
      linarith
    unfold alcAr
    exact mul_nonneg h1 (tsum_nonneg fun n => by positivity)
  rw [Real.dist_eq] at a1 ⊢
  have hδmul : δ * (ℓ + 1) = ε / 4 := by
    rw [hδ]; field_simp
  have hb1 : δ * alcAr u (fun _ => 1) α ≤ ε / 4 := by
    rw [← hδmul]; exact mul_le_mul_of_nonneg_left a2.le hδpos.le
  have hb2 : ℓ * δ ≤ ε / 4 := by
    rw [← hδmul]; nlinarith
  have k1 := abs_le.mp (hdiff.trans hb1)
  have k2 := abs_le.mp a1.le
  have k3 := abs_le.mp (hint.trans hb2)
  have k4 := abs_lt.mp a1
  rw [abs_sub_lt_iff]
  constructor <;> linarith [k1.1, k1.2, k3.1, k3.2, k4.1, k4.2]

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) (f : ℝ → ℝ)
    (hf : ContinuousOn f (Set.Icc 0 1)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ)) * ∑' n : ℕ, (α : ℝ) ^ n * (u n).toReal * f ((α : ℝ) ^ n))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L.toReal * ∫ x in (0 : ℝ)..1, f x)) :=
  alc_main u hu0 L hL hlim f hf


