-- Prove2me | solution 1 for SennottDP.Tauberian.abel_limit_r
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-03T18:01:35.827976+00:00
-- url     : https://prove2.me/submissions/cc24268a-d599-4da7-bfb0-2c3b334c871a

import Mathlib
import Definitions.Def_SennottDP_Tauberian_PowerSeries
import Definitions.Def_SennottDP_Tauberian_KaramataR
import Theorems.Thm_SennottDP_Tauberian_abel_limit_continuous
import Theorems.Thm_SennottDP_Tauberian_continuous_sandwich_r
import Theorems.Thm_SennottDP_Tauberian_integral_r

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


theorem alr_r_nonneg (x : ℝ) (hx : 0 ≤ x) : 0 ≤ r x := by
  unfold r; split_ifs <;> positivity

theorem alr_r_bound (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) : |r x| ≤ Real.exp 1 := by
  rw [abs_of_nonneg (alr_r_nonneg x hx.1)]
  unfold r
  split_ifs with h
  · have hpos : 0 < Real.exp (-1) := Real.exp_pos _
    calc x⁻¹ ≤ (Real.exp (-1))⁻¹ := inv_anti₀ hpos h
      _ = Real.exp 1 := by rw [Real.exp_neg, inv_inv]
  · exact (Real.exp_pos 1).le

theorem alr_r_one : r 1 = 1 := by
  unfold r
  rw [if_pos (by rw [Real.exp_le_one_iff]; norm_num), inv_one]

theorem alr_sub (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : alcGood u α) (g₁ g₂ : ℝ → ℝ) (B₁ B₂ : ℝ)
    (h₁ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g₁ x| ≤ B₁) (h₂ : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g₂ x| ≤ B₂) :
    alcAr u (fun x => g₁ x - g₂ x) α = alcAr u g₁ α - alcAr u g₂ α := by
  unfold alcAr
  rw [← mul_sub, ← (alc_summable_of_bound h g₁ B₁ h₁).tsum_sub
    (alc_summable_of_bound h g₂ B₂ h₂)]
  congr 1
  exact tsum_congr fun n => by ring

theorem alr_le_head (u : ℕ → ℝ≥0∞) {α : ℝ≥0} (h : alcGood u α) (g : ℝ → ℝ) (B : ℝ)
    (hB : ∀ x ∈ Set.Icc (0 : ℝ) 1, |g x| ≤ B) (hneg : ∀ x ∈ Set.Ioo (0 : ℝ) 1, g x ≤ 0) :
    alcAr u g α ≤ (1 - (α : ℝ)) * ((u 0).toReal * g 1) := by
  unfold alcAr
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    linarith
  refine mul_le_mul_of_nonneg_left ?_ h1
  rw [(alc_summable_of_bound h g B hB).tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  have : ∑' n : ℕ, (α : ℝ) ^ (n + 1) * (u (n + 1)).toReal * g ((α : ℝ) ^ (n + 1)) ≤ 0 := by
    refine tsum_nonpos fun n => ?_
    have hα0 : (0 : ℝ) < α := by exact_mod_cast h.1
    have hα1 : (α : ℝ) < 1 := by exact_mod_cast h.2.1
    have hmem : (α : ℝ) ^ (n + 1) ∈ Set.Ioo (0 : ℝ) 1 :=
      ⟨by positivity, pow_lt_one₀ hα0.le hα1 (by omega)⟩
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (hneg _ hmem)
  linarith

theorem alr_tendsto_zero (K : ℝ) :
    Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ)) * K) (𝓝[<] (1 : ℝ≥0)) (𝓝 0) := by
  have : Tendsto (fun α : ℝ≥0 => (1 - (α : ℝ)) * K) (𝓝 (1 : ℝ≥0)) (𝓝 ((1 - ((1 : ℝ≥0) : ℝ)) * K)) :=
    ((continuous_const.sub NNReal.continuous_coe).mul continuous_const).tendsto 1
  simp only [NNReal.coe_one, sub_self, zero_mul] at this
  exact this.mono_left nhdsWithin_le_nhds

theorem alr_real (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (alcAr u r) (𝓝[<] (1 : ℝ≥0)) (𝓝 L.toReal) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set ℓ := L.toReal
  have hℓ : 0 ≤ ℓ := ENNReal.toReal_nonneg
  set ε1 := ε / (4 * (ℓ + 1)) with hε1
  have hε1pos : 0 < ε1 := by positivity
  have hℓε1 : ℓ * ε1 ≤ ε / 4 := by
    have : ε1 * (ℓ + 1) = ε / 4 := by rw [hε1]; field_simp
    nlinarith
  obtain ⟨s, ss, hs, hss, hsr, hI1, -, hI3⟩ := continuous_sandwich_r ε1 hε1pos
  obtain ⟨Bs, hBs⟩ := alc_bound_of_contOn s hs
  obtain ⟨Bss, hBss⟩ := alc_bound_of_contOn ss hss
  have ts := abel_limit_continuous u hu0 L hL hlim s hs
  have tss := abel_limit_continuous u hu0 L hL hlim ss hss
  have e1 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), alcAr u s α < ℓ * (∫ x in (0 : ℝ)..1, s x) + ε / 4 :=
    ts.eventually (gt_mem_nhds (by linarith))
  have e2 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0), ℓ * (∫ x in (0 : ℝ)..1, ss x) - ε / 4 < alcAr u ss α :=
    tss.eventually (lt_mem_nhds (by linarith))
  have e3 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      (1 - (α : ℝ)) * ((u 0).toReal * |r 1 - s 1|) < ε / 4 :=
    (alr_tendsto_zero _).eventually (gt_mem_nhds (by positivity))
  have e4 : ∀ᶠ α : ℝ≥0 in 𝓝[<] (1 : ℝ≥0),
      (1 - (α : ℝ)) * ((u 0).toReal * |ss 1 - r 1|) < ε / 4 :=
    (alr_tendsto_zero _).eventually (gt_mem_nhds (by positivity))
  filter_upwards [e1, e2, e3, e4, alc_eventually_good u L hL hlim] with α a1 a2 a3 a4 hα
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
    linarith
  have hu0' : 0 ≤ (u 0).toReal := ENNReal.toReal_nonneg
  -- upper
  have up := alr_le_head u hα (fun x => r x - s x) (Real.exp 1 + Bs)
    (fun x hx => (abs_sub _ _).trans (add_le_add (alr_r_bound x hx) (hBs x hx)))
    (fun x hx => sub_nonpos.mpr (hsr x hx).2)
  rw [alr_sub u hα r s _ _ alr_r_bound hBs] at up
  have up2 : (1 - (α : ℝ)) * ((u 0).toReal * (r 1 - s 1)) ≤
      (1 - (α : ℝ)) * ((u 0).toReal * |r 1 - s 1|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hu0') h1
  -- lower
  have lo := alr_le_head u hα (fun x => ss x - r x) (Bss + Real.exp 1)
    (fun x hx => (abs_sub _ _).trans (add_le_add (hBss x hx) (alr_r_bound x hx)))
    (fun x hx => sub_nonpos.mpr (hsr x hx).1)
  rw [alr_sub u hα ss r _ _ hBss alr_r_bound] at lo
  have lo2 : (1 - (α : ℝ)) * ((u 0).toReal * (ss 1 - r 1)) ≤
      (1 - (α : ℝ)) * ((u 0).toReal * |ss 1 - r 1|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self _) hu0') h1
  have i1 : ℓ * (∫ x in (0 : ℝ)..1, s x) ≤ ℓ * (1 + ε1) := mul_le_mul_of_nonneg_left hI3 hℓ
  have i2 : ℓ * (1 - ε1) ≤ ℓ * (∫ x in (0 : ℝ)..1, ss x) := mul_le_mul_of_nonneg_left hI1 hℓ
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> nlinarith

end SennottDP.Tauberian

open SennottDP.Tauberian in
theorem solution (u : ℕ → ℝ≥0∞) (hu0 : u 0 ≠ ⊤) (L : ℝ≥0∞) (hL : L ≠ ⊤)
    (hlim : Tendsto (abelMean u) (𝓝[<] (1 : ℝ≥0)) (𝓝 L)) :
    Tendsto (fun α : ℝ≥0 =>
        (1 - (α : ℝ≥0∞)) * ∑' n : ℕ, (α : ℝ≥0∞) ^ n * u n * ENNReal.ofReal (r ((α : ℝ) ^ n)))
      (𝓝[<] (1 : ℝ≥0)) (𝓝 (L * ENNReal.ofReal (∫ x in (0 : ℝ)..1, r x))) := by
  have hI : ∫ x in (0 : ℝ)..1, r x = 1 := integral_r.1.trans integral_r.2
  rw [hI, ENNReal.ofReal_one, mul_one]
  have ht := ENNReal.tendsto_ofReal (alr_real u hu0 L hL hlim)
  rw [ENNReal.ofReal_toReal hL] at ht
  refine ht.congr' ?_
  filter_upwards [alc_eventually_good u L hL hlim] with α hα
  have h1 : 0 ≤ 1 - (α : ℝ) := by
    have : (α : ℝ) < 1 := by exact_mod_cast hα.2.1
    linarith
  unfold alcAr
  rw [ENNReal.ofReal_mul h1]
  have hsub : ENNReal.ofReal (1 - (α : ℝ)) = 1 - (α : ℝ≥0∞) := by
    rw [← NNReal.coe_one, ← NNReal.coe_sub hα.2.1.le, ENNReal.ofReal_coe_nnreal,
      ENNReal.coe_sub, ENNReal.coe_one]
  rw [hsub]
  congr 1
  · rw [ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (by positivity)
      (alr_r_nonneg _ (by positivity))) (alc_summable_of_bound hα r _ alr_r_bound)]
    refine tsum_congr fun n => ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_toReal (alcGood_fin hα n), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_coe_nnreal]


