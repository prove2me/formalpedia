-- Prove2me | solution 1 for SinglePointPricing.Det.propD1_worst_terms
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-29T09:31:36.077804+00:00
-- url     : https://prove2.me/submissions/ee601948-ea2c-4ddb-b73b-17ba9f8ab9b6

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase
import Theorems.Thm_SinglePointPricing_Det_lemma_C_2

namespace SPPD
open SinglePointPricing.Det

lemma GA_pos (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_pos _
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_pos_of_pos; nlinarith

lemma GA_zero (α : ℝ) : GammaA α 0 = 1 := by
  unfold GammaA; split_ifs <;> simp

lemma GAInv_GA (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    GammaAInv α (GammaA α x) = x := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 ≤ 1 + (1 - α) * x := by nlinarith
    rw [← Real.rpow_mul hb]
    have : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
    rw [this, Real.rpow_one]; field_simp; ring

lemma GAInv_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < GammaAInv α q := by
  rcases hq with ⟨h0, h1⟩
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_neg h0 h1; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_pos _ ha
    have : 1 < q ^ (-(1 - α)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
    linarith

lemma GAInv_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x < y) :
    GammaAInv α y < GammaAInv α x := by
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_lt_log hx hxy; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_lt_div_of_pos_right _ ha
    have := Real.rpow_lt_rpow_of_neg hx hxy (by linarith : -(1 - α) < 0)
    linarith

lemma one_add_kc (α q : ℝ) (hq : 0 < q) :
    1 + (1 - α) * GammaAInv α q = q ^ (α - 1) := by
  unfold GammaAInv
  split_ifs with h
  · subst h; simp
  · have ha : (1 - α) ≠ 0 := by intro h'; apply h; linarith
    have : -(1 - α) = α - 1 := by ring
    rw [this]; field_simp; ring

lemma log_GA (α v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hv : 0 ≤ v) (hα1 : α ≠ 1) :
    Real.log (GammaA α v) = -(1 / (1 - α)) * Real.log (1 + (1 - α) * v) := by
  have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 hα1)
  unfold GammaA; rw [if_neg hα1, Real.log_rpow (by nlinarith)]

lemma logGA_tangent (α v v0 : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hv : 0 ≤ v) (hv0 : 0 ≤ v0) :
    Real.log (GammaA α v0) - (v - v0) / (1 + (1 - α) * v0) ≤ Real.log (GammaA α v) := by
  by_cases h1 : α = 1
  · subst h1; unfold GammaA; simp
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1)
    rw [log_GA α v hα hv h1, log_GA α v0 hα hv0 h1]
    have hx : 0 < 1 + (1 - α) * v := by nlinarith
    have hy : 0 < 1 + (1 - α) * v0 := by nlinarith
    have hl := Real.log_le_sub_one_of_pos (div_pos hx hy)
    rw [Real.log_div hx.ne' hy.ne'] at hl
    have e1 : (1 + (1 - α) * v) / (1 + (1 - α) * v0) - 1
        = (1 - α) * ((v - v0) / (1 + (1 - α) * v0)) := by field_simp; ring
    rw [e1] at hl
    set t := (v - v0) / (1 + (1 - α) * v0)
    have e : 1 / (1 - α) * (Real.log (1 + (1 - α) * v) - Real.log (1 + (1 - α) * v0)) ≤ t := by
      rw [one_div, inv_mul_le_iff₀ hk]; linarith
    nlinarith

lemma Fbar_lt (α q r p : ℝ) (hr1 : r < 1) (hrp : r ≤ p) (hp1 : p ≤ 1) :
    Fbar α 1 q r p = GammaA α (GammaAInv α q * (p - r) / (1 - r)) := by
  simp [Fbar, hr1, Gbar, not_lt.mpr hrp, hp1]

lemma Fbar_ge (α q r p : ℝ) (hr1 : 1 ≤ r) (hp0 : 0 ≤ p) (hpr : p ≤ r) :
    Fbar α 1 q r p = GammaA α (GammaAInv α q * p) := by
  simp [Fbar, not_lt.mpr hr1, Gbar, not_lt.mpr hp0, hpr]

lemma optFun_of_max (F : ℝ → ℝ) (r : ℝ) (hr : 0 ≤ r)
    (hmax : IsMaxOn (fun v => v * F v) (Set.Ici 0) r) : optFun F = r * F r := by
  unfold optFun
  apply IsGreatest.csSup_eq
  refine ⟨⟨r, hr, rfl⟩, ?_⟩
  rintro _ ⟨v, hv, rfl⟩
  exact hmax hv

lemma optFun_r (α q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hr : r ∈ rSet α 1 q) : optFun (Fbar α 1 q r) = r * Fbar α 1 q r r := by
  obtain ⟨h0, hmax⟩ := lemma_C_2 α 1 q r hα one_pos hq hr
  exact optFun_of_max _ r h0 hmax

lemma rLow_eq (α q : ℝ) : rLow α 1 q = 1 / (GammaAInv α q + 1) := rfl

/-- the facts on `µ_{α,q}(p)` used in (D-5). -/
lemma mu_facts (α q p : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hp : p ∈ Set.Ioo (rLow α 1 q) 1) :
    rLow α 1 q ≤ muAQ α q p ∧ muAQ α q p < p ∧
      GammaAInv α q * (1 - p) * muAQ α q p =
        (1 - muAQ α q p) * (1 - muAQ α q p + (1 - α) * GammaAInv α q * (p - muAQ α q p)) := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have ha_eq := one_add_kc α q hq.1
  rw [← hc_def] at ha_eq
  set a := q ^ (α - 1) with ha_def
  have hapos : 0 < a := by rw [← ha_eq]; nlinarith [hα.2]
  have hp1 : 0 < 1 - p := by linarith [hp.2]
  have hpl : 1 < p * (c + 1) := by
    have h := hp.1; rw [rLow_eq, div_lt_iff₀ (by linarith)] at h; linarith
  set b := α * c * (1 - p) with hb_def
  set d := c * (1 - p) with hd_def
  have hb0 : 0 ≤ b := by have := hα.1; positivity
  have hd0 : 0 < d := by positivity
  have hDelta : Delta α q p = b ^ 2 + 4 * d * a := by
    simp only [Delta, hb_def, hd_def, ← hc_def, ha_def]; ring
  have hD0 : 0 ≤ Delta α q p := by rw [hDelta]; positivity
  set S := Real.sqrt (Delta α q p) with hS_def
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS2 : S ^ 2 = b ^ 2 + 4 * d * a := by rw [hS_def, Real.sq_sqrt hD0, hDelta]
  have hmu : muAQ α q p = 1 - (S - b) / (2 * a) := by
    simp only [muAQ, hS_def, hb_def, ← hc_def, ha_def]
  set s := (S - b) / (2 * a) with hs_def
  have hs2 : 2 * a * s = S - b := by rw [hs_def]; field_simp
  have hquad : a * s ^ 2 + b * s - d = 0 := by
    have h4 : 4 * a * (a * s ^ 2 + b * s - d) = 0 := by
      have hSe : S = 2 * a * s + b := by linarith
      rw [hSe] at hS2; linear_combination hS2
    rcases mul_eq_zero.mp h4 with h | h
    · exfalso; linarith
    · exact h
  have hSb : b ≤ S := by
    by_contra hcon; push Not at hcon
    nlinarith [mul_pos hd0 hapos]
  have hs0 : 0 ≤ s := by rw [hs_def]; apply div_nonneg <;> linarith
  rw [hmu]
  refine ⟨?_, ?_, ?_⟩
  · -- s ≤ c/(c+1)
    rw [rLow_eq, ← hc_def]
    have hs_le : s ≤ c / (c + 1) := by
      by_contra hcon; push Not at hcon
      set s0 := c / (c + 1) with hs0_def
      have hs0pos : 0 < s0 := by positivity
      have hf0 : 0 ≤ a * s0 ^ 2 + b * s0 - d := by
        have e : (c + 1) ^ 2 * (a * s0 ^ 2 + b * s0 - d) = c * a * (p * (c + 1) - 1) := by
          rw [hs0_def, hb_def, hd_def, ← ha_eq]; field_simp; ring
        have : 0 ≤ c * a * (p * (c + 1) - 1) := by
          apply mul_nonneg (by positivity); linarith
        rw [← e] at this
        exact (mul_nonneg_iff_of_pos_left (by positivity)).mp this
      nlinarith [mul_pos (sub_pos.mpr hcon) (by positivity : 0 < a * (s + s0) + b)]
    have : 1 / (c + 1) = 1 - c / (c + 1) := by field_simp; ring
    rw [this]; linarith
  · -- µ < p, i.e. 1 - p < s
    by_contra hcon; push Not at hcon
    have hsle : s ≤ 1 - p := by linarith
    have hf1 : a * (1 - p) ^ 2 + b * (1 - p) - d = (1 - p) * (1 - p * (c + 1)) := by
      rw [hb_def, hd_def, ← ha_eq]; ring
    have hneg : (1 - p) * (1 - p * (c + 1)) < 0 := mul_neg_of_pos_of_neg hp1 (by linarith)
    nlinarith [mul_nonneg (sub_nonneg.mpr hsle) (by positivity : 0 ≤ a * (1 - p + s) + b)]
  · have e1 : 1 - (1 - s) = s := by ring
    rw [e1]
    rw [← ha_eq] at hquad
    linear_combination (-1 : ℝ) * hquad

/-- (D-5): the first worst-case term. -/
theorem first_term (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (p : ℝ) (hp : p ∈ Set.Ioo (rLow α 1 q) 1) :
    IsLeast ((fun r => p * Fbar α 1 q r p / r) '' Set.Ico (rLow α 1 q) p) (R1 α q p) := by
  obtain ⟨hmuL, hmup, hcrit⟩ := mu_facts α q p hα hq hp
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  set μ := muAQ α q p with hμ_def
  have hL0 : 0 < rLow α 1 q := by rw [rLow_eq]; positivity
  have hμ0 : 0 < μ := lt_of_lt_of_le hL0 hmuL
  have hp1 : p < 1 := hp.2
  have hμ1 : μ < 1 := lt_trans hmup hp1
  have hp0 : 0 < p := lt_trans hμ0 hmup
  have hk : 0 ≤ 1 - α := by linarith [hα.2]
  -- R1 = Φ(µ)
  have hμset : μ ∈ rSet α 1 q := Or.inl ⟨hmuL, hμ1⟩
  have hopt : optFun (Fbar α 1 q μ) = μ := by
    rw [optFun_r α q μ hα hq hμset, Fbar_lt α q μ μ hμ1 le_rfl hμ1.le]
    simp [GA_zero]
  have hR1 : R1 α q p = p * Fbar α 1 q μ p / μ := by
    unfold R1; rw [← hμ_def, hopt]
  refine ⟨⟨μ, ⟨hmuL, hmup⟩, hR1.symm⟩, ?_⟩
  rintro _ ⟨r, ⟨hrL, hrp⟩, rfl⟩
  have hr0 : 0 < r := lt_of_lt_of_le hL0 hrL
  have hr1 : r < 1 := lt_trans hrp hp1
  rw [hR1]
  simp only
  rw [Fbar_lt α q μ p hμ1 hmup.le hp1.le, Fbar_lt α q r p hr1 hrp.le hp1.le]
  set vr := c * (p - r) / (1 - r) with hvr
  set vμ := c * (p - μ) / (1 - μ) with hvμ
  have hvr0 : 0 ≤ vr := by
    rw [hvr]; apply div_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
  have hvμ0 : 0 ≤ vμ := by
    rw [hvμ]; apply div_nonneg (mul_nonneg hc.le (by linarith)) (by linarith)
  have hGr := GA_pos α vr hα hvr0
  have hGμ := GA_pos α vμ hα hvμ0
  have hA : 0 < 1 + (1 - α) * vμ := by nlinarith
  -- log inequality
  have htan := logGA_tangent α vr vμ hα hvr0 hvμ0
  have hlogr : Real.log r - Real.log μ ≤ r / μ - 1 := by
    rw [← Real.log_div hr0.ne' hμ0.ne']; exact Real.log_le_sub_one_of_pos (div_pos hr0 hμ0)
  have hB : 0 < 1 - μ + (1 - α) * c * (p - μ) := by
    have : 0 ≤ (1 - α) * c * (p - μ) := mul_nonneg (mul_nonneg hk hc.le) (by linarith)
    linarith
  have hr1' : 1 - r ≠ 0 := by linarith
  have hμ1' : 1 - μ ≠ 0 := by linarith
  have key : (vr - vμ) / (1 + (1 - α) * vμ) + (r / μ - 1) ≤ 0 := by
    have h1 : vr - vμ = c * (1 - p) * (μ - r) / ((1 - μ) * (1 - r)) := by
      rw [hvr, hvμ]; field_simp; ring
    have hAe : 1 + (1 - α) * vμ = (1 - μ + (1 - α) * c * (p - μ)) / (1 - μ) := by
      rw [hvμ]; field_simp
    have h2 : c * (1 - p) = (1 - μ) * (1 - μ + (1 - α) * c * (p - μ)) / μ := by
      field_simp; linarith [hcrit]
    have h3 : (vr - vμ) / (1 + (1 - α) * vμ) = (1 - μ) * (μ - r) / (μ * (1 - r)) := by
      rw [h1, hAe, h2]
      have : (1 - r) ≠ 0 := by linarith
      have : (1 - μ) ≠ 0 := by linarith
      field_simp
    rw [h3]
    have h4 : (1 - μ) * (μ - r) / (μ * (1 - r)) + (r / μ - 1)
        = -((r - μ) ^ 2 / (μ * (1 - r))) := by
      have : (1 - r) ≠ 0 := by linarith
      field_simp; ring
    rw [h4]
    have : 0 ≤ (r - μ) ^ 2 / (μ * (1 - r)) :=
      div_nonneg (sq_nonneg _) (mul_nonneg hμ0.le (by linarith))
    linarith
  -- conclude
  have hpos1 : 0 < p * (GammaA α vμ) / μ := by positivity
  have hpos2 : 0 < p * (GammaA α vr) / r := by positivity
  rw [← Real.log_le_log_iff hpos1 hpos2, Real.log_div (by positivity) hμ0.ne',
    Real.log_div (by positivity) hr0.ne', Real.log_mul hp0.ne' hGμ.ne',
    Real.log_mul hp0.ne' hGr.ne']
  have : (vr - vμ) / (1 + (1 - α) * vμ) ≤ -(r / μ - 1) := by linarith
  linarith

lemma GA0 (x : ℝ) : GammaA 0 x = (1 + x)⁻¹ := by
  unfold GammaA; norm_num; rw [Real.rpow_neg_one]

lemma GA1 (x : ℝ) : GammaA 1 x = Real.exp (-x) := by
  unfold GammaA; norm_num

/-- the revenue `x ↦ x Γ_α(c x)` is maximized over `(0, r̄]` at `r̄ = 1/(α c)`. -/
lemma rev_le_rbar (α c r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hα0 : α ≠ 0) (hc : 0 < c)
    (hr0 : 0 < r) (hr : α * c * r ≤ 1) :
    r * GammaA α (c * r) ≤ 1 / (α * c) * GammaA α (c * (1 / (α * c))) := by
  have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
  have hrb : 0 < 1 / (α * c) := by positivity
  have hcr : 0 ≤ c * r := by positivity
  have hcrb : 0 ≤ c * (1 / (α * c)) := by positivity
  have h1 := GA_pos α (c * r) hα hcr
  have h2 := GA_pos α (c * (1 / (α * c))) hα hcrb
  rw [← Real.log_le_log_iff (by positivity) (by positivity), Real.log_mul hr0.ne' h1.ne',
    Real.log_mul hrb.ne' h2.ne']
  set t := α * c * r with ht
  have ht0 : 0 < t := by positivity
  have hcb : c * (1 / (α * c)) = 1 / α := by field_simp
  have hlogrb : Real.log (1 / (α * c)) = Real.log r - Real.log t := by
    rw [ht, Real.log_mul (by positivity) hr0.ne', Real.log_div one_ne_zero (by positivity)]
    simp
  rw [hlogrb, hcb]
  by_cases h1α : α = 1
  · subst h1α
    rw [GA1, GA1, Real.log_exp, Real.log_exp]
    have : c * r = t := by rw [ht]; ring
    rw [this]
    have := Real.log_le_sub_one_of_pos ht0
    norm_num; linarith
  · have hk : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h1α)
    rw [log_GA α _ hα hcr h1α, log_GA α _ hα (by positivity) h1α]
    have hx : 0 < 1 + (1 - α) * (c * r) := by nlinarith
    have hy : 0 < 1 + (1 - α) * (1 / α) := by positivity
    -- k log t ≤ log (1 + k c r) - log (1 + k/α)
    have hber := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hk.le
      (by linarith)
    have hb2 : 1 + (t - 1) = t := by ring
    rw [hb2] at hber
    have hpos : 0 < t ^ (1 - α) := Real.rpow_pos_of_pos ht0 _
    have hl := Real.log_le_log hpos hber
    rw [Real.log_rpow ht0] at hl
    have hq1 : 1 + (1 - α) * (t - 1) = (1 + (1 - α) * (c * r)) / (1 + (1 - α) * (1 / α)) := by
      rw [ht]; field_simp; ring
    rw [hq1, Real.log_div hx.ne' hy.ne'] at hl
    have e : 1 / (1 - α) * ((1 - α) * Real.log t) = Real.log t := by field_simp
    have hl2 : Real.log t ≤ 1 / (1 - α) *
        (Real.log (1 + (1 - α) * (c * r)) - Real.log (1 + (1 - α) * (1 / α))) := by
      rw [← e]; exact mul_le_mul_of_nonneg_left hl (by positivity)
    nlinarith

/-- (D-4): the third worst-case term. -/
theorem third_term (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1)
    (hqL : qLow α ≤ q) (p : ℝ) (hp : p ∈ Set.Icc (0 : ℝ) 1) :
    IsGLB ((fun r => p * Fbar α 1 q r p / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}) (R3 α q p) := by
  have hc := GAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  have helt : ∀ r, 1 ≤ r → α * c * r ≤ 1 →
      p * Fbar α 1 q r p / optFun (Fbar α 1 q r) = p * GammaA α (c * p) / (r * GammaA α (c * r)) := by
    intro r hr1 hr2
    rw [optFun_r α q r hα hq (Or.inr ⟨hr1, hr2⟩), Fbar_ge α q r p hr1 hp.1 (by linarith [hp.2]),
      Fbar_ge α q r r hr1 (by linarith) le_rfl]
  have hX : 0 ≤ p * GammaA α (c * p) := mul_nonneg hp.1 (GA_pos α _ hα (by nlinarith [hp.1])).le
  by_cases hα0 : α = 0
  · subst hα0
    have hR3 : R3 0 q p = c * (p * GammaA 0 (c * p)) := by
      simp [R3, vTilde, ← hc_def]
    rw [hR3]
    set X := p * GammaA 0 (c * p) with hXdef
    have helt0 : ∀ r, 1 ≤ r → p * Fbar 0 1 q r p / optFun (Fbar 0 1 q r) = X / r + c * X := by
      intro r hr1
      rw [helt r hr1 (by simp), GA0]
      have : 0 < r := by linarith
      field_simp
      try ring
    constructor
    · rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
      dsimp only
      rw [helt0 r hr1]
      have : 0 ≤ X / r := div_nonneg hX (by linarith)
      linarith
    · intro b hb
      by_contra hcon; push Not at hcon
      set D := b - c * X with hD
      have hD0 : 0 < D := by linarith
      set r := 1 + X / D with hr
      have hr1 : 1 ≤ r := by have : 0 ≤ X / D := div_nonneg hX hD0.le; linarith
      have hmem : X / r + c * X ∈ ((fun r => p * Fbar 0 1 q r p / optFun (Fbar 0 1 q r)) ''
          {r | 1 ≤ r ∧ 0 * GammaAInv 0 q * r ≤ 1}) := ⟨r, ⟨hr1, by simp⟩, helt0 r hr1⟩
      have hle := hb hmem
      have hlt : X / r < D := by
        rw [div_lt_iff₀ (by linarith), hr]
        rw [mul_add, mul_div_cancel₀ _ hD0.ne']
        linarith
      linarith
  · have hαp : 0 < α := lt_of_le_of_ne hα.1 (Ne.symm hα0)
    have hac : α * c ≤ 1 := by
      have hqL' : GammaA α (1 / α) ≤ q := by simpa [qLow, hα0] using hqL
      have hc1 : c ≤ 1 / α := by
        rcases eq_or_lt_of_le hqL' with h | h
        · rw [hc_def, ← h, GAInv_GA α _ hα (by positivity)]
        · have := GAInv_anti α _ _ hα (GA_pos α _ hα (by positivity)) h
          rw [GAInv_GA α _ hα (by positivity)] at this
          exact this.le
      rw [le_div_iff₀ hαp] at hc1; linarith
    have hrb1 : 1 ≤ 1 / (α * c) := by rw [le_div_iff₀ (by positivity)]; linarith
    have hrb2 : α * c * (1 / (α * c)) ≤ 1 := by
      rw [mul_one_div_cancel (by positivity)]
    have hR3 : R3 α q p = p * Fbar α 1 q (1 / (α * c)) p / optFun (Fbar α 1 q (1 / (α * c))) := by
      simp [R3, hα0, ← hc_def]
    rw [hR3]
    apply IsLeast.isGLB
    refine ⟨⟨1 / (α * c), ⟨hrb1, hrb2⟩, rfl⟩, ?_⟩
    rintro _ ⟨r, ⟨hr1, hr2⟩, rfl⟩
    simp only
    rw [helt r hr1 hr2, helt _ hrb1 hrb2]
    apply div_le_div_of_nonneg_left hX
    · exact mul_pos (by linarith) (GA_pos α _ hα (by nlinarith))
    · exact rev_le_rbar α c r hα hα0 hc (by linarith) hr2

theorem main (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ p ∈ Set.Ioo (rLow α 1 q) 1,
      IsLeast ((fun r => p * Fbar α 1 q r p / r) '' Set.Ico (rLow α 1 q) p) (R1 α q p)) ∧
    (qLow α ≤ q → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      IsGLB ((fun r => p * Fbar α 1 q r p / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}) (R3 α q p)) :=
  ⟨fun p hp => first_term α hα q hq p hp, fun hqL p hp => third_term α hα q hq hqL p hp⟩

end SPPD

open SinglePointPricing.Det in
theorem solution (α : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (q : ℝ)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ p ∈ Set.Ioo (rLow α 1 q) 1,
      IsLeast ((fun r => p * Fbar α 1 q r p / r) '' Set.Ico (rLow α 1 q) p) (R1 α q p)) ∧
    (qLow α ≤ q → ∀ p ∈ Set.Icc (0 : ℝ) 1,
      IsGLB ((fun r => p * Fbar α 1 q r p / optFun (Fbar α 1 q r)) ''
        {r | 1 ≤ r ∧ α * GammaAInv α q * r ≤ 1}) (R3 α q p)) :=
  SPPD.main α hα q hq
