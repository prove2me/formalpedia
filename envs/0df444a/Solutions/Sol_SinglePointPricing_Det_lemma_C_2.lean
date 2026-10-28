-- Prove2me | solution 1 for SinglePointPricing.Det.lemma_C_2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-27T03:52:58.336323+00:00
-- url     : https://prove2.me/submissions/97e28406-e1ef-4328-bdeb-db4cbeb7dbb3

import Mathlib
import Definitions.Def_SinglePointPricing_Det_Setting
import Definitions.Def_SinglePointPricing_Det_WorstCase

open SinglePointPricing.Det MeasureTheory

lemma hGA_pos (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) : 0 < GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_pos _
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_pos_of_pos; nlinarith

lemma hGA_zero (α : ℝ) : GammaA α 0 = 1 := by
  unfold GammaA; split_ifs <;> simp

lemma hGAInv_one (α : ℝ) : GammaAInv α 1 = 0 := by
  unfold GammaAInv; split_ifs <;> simp

lemma hGAInv_GA (α x : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) :
    GammaAInv α (GammaA α x) = x := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hb : 0 ≤ 1 + (1 - α) * x := by nlinarith
    rw [← Real.rpow_mul hb]
    have : -(1 / (1 - α)) * -(1 - α) = 1 := by field_simp
    rw [this, Real.rpow_one]; field_simp; ring

lemma hGA_GAInv (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : 0 < q) :
    GammaA α (GammaAInv α q) = q := by
  unfold GammaA GammaAInv
  split_ifs with h
  · simp [Real.exp_log hq]
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have : 1 + (1 - α) * ((q ^ (-(1 - α)) - 1) / (1 - α)) = q ^ (-(1 - α)) := by
      field_simp; ring
    rw [this, ← Real.rpow_mul hq.le]
    have : -(1 - α) * -(1 / (1 - α)) = 1 := by field_simp
    rw [this, Real.rpow_one]

lemma hGAInv_pos (α q : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    0 < GammaAInv α q := by
  rcases hq with ⟨h0, h1⟩
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_neg h0 h1; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_pos _ ha
    have : 1 < q ^ (-(1 - α)) := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (by linarith)
    linarith

/-- strict antitonicity of GammaAInv on (0, ∞) -/
lemma hGAInv_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 < x) (hxy : x < y) :
    GammaAInv α y < GammaAInv α x := by
  unfold GammaAInv
  split_ifs with h
  · have := Real.log_lt_log hx hxy; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply div_lt_div_of_pos_right _ ha
    have := Real.rpow_lt_rpow_of_neg hx hxy (by linarith : -(1 - α) < 0)
    linarith

lemma hGA_anti (α x y : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hx : 0 ≤ x) (hxy : x ≤ y) :
    GammaA α y ≤ GammaA α x := by
  unfold GammaA
  split_ifs with h
  · exact Real.exp_le_exp.mpr (by linarith)
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    apply Real.rpow_le_rpow_of_nonpos (by nlinarith) (by nlinarith)
    have : 0 < 1 / (1 - α) := by positivity
    linarith

lemma lemA (α β r v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hr : 0 < r) (hβ : 1 ≤ β * r)
    (hv : r ≤ v) : v * GammaA α (β * (v - r)) ≤ r := by
  have hβ0 : 0 < β := by
    by_contra h; push_neg at h; nlinarith
  unfold GammaA
  split_ifs with h
  · have h1 := Real.add_one_le_exp (β * (v - r))
    have h2 : v ≤ r * Real.exp (β * (v - r)) := by nlinarith
    have he : Real.exp (-(β * (v - r))) = (Real.exp (β * (v - r)))⁻¹ := Real.exp_neg _
    rw [he]
    have hp := Real.exp_pos (β * (v - r))
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; linarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    set a := 1 - α with ha_def
    have ha1 : a ≤ 1 := by rcases hα with ⟨h0, _⟩; linarith
    set B := 1 + a * (β * (v - r)) with hB
    have hB1 : 1 ≤ B := by have : 0 ≤ a * (β * (v - r)) := by
                              apply mul_nonneg ha.le; apply mul_nonneg hβ0.le; linarith
                           linarith
    have hBp : 0 < B := by linarith
    -- Bernoulli
    have hbern := rpow_one_add_le_one_add_mul_self (s := (v - r) / r)
      (by have : 0 ≤ (v - r) / r := div_nonneg (by linarith) hr.le
          linarith) ha.le ha1
    have e1 : 1 + (v - r) / r = v / r := by field_simp; ring
    rw [e1] at hbern
    have h2 : a * ((v - r) / r) ≤ a * (β * (v - r)) := by
      apply mul_le_mul_of_nonneg_left _ ha.le
      rw [div_le_iff₀ hr]; nlinarith
    have h3 : (v / r) ^ a ≤ B := by linarith
    have hvr : 0 ≤ v / r := div_nonneg (by linarith) hr.le
    have h4 : v / r ≤ B ^ (1 / a) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hvr a) h3 (by positivity : (0:ℝ) ≤ 1 / a)
      rwa [← Real.rpow_mul hvr, mul_one_div_cancel ha.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hBp.le]
    have hp : 0 < B ^ (1 / a) := Real.rpow_pos_of_pos hBp _
    rw [← div_eq_mul_inv, div_le_iff₀ hp]
    rw [div_le_iff₀ hr] at h4; linarith

lemma lemB (α β r v : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hβ : 0 ≤ β) (hαβ : α * β * r ≤ 1)
    (hv0 : 0 ≤ v) (hvr : v ≤ r) : v * GammaA α (β * v) ≤ r * GammaA α (β * r) := by
  rcases eq_or_lt_of_le hv0 with hv | hv
  · rw [← hv, zero_mul]
    exact mul_nonneg (by linarith) (hGA_pos α _ hα (by nlinarith)).le
  have hr : 0 < r := by linarith
  unfold GammaA
  split_ifs with h
  · subst h
    have hlog : β * (r - v) ≤ Real.log (r / v) := by
      have := Real.one_sub_inv_le_log_of_pos (div_pos hr hv)
      rw [inv_div] at this
      have e : 1 - v / r = (r - v) / r := by field_simp
      rw [e] at this
      have : β * (r - v) ≤ (r - v) / r := by
        rw [le_div_iff₀ hr]; nlinarith
      linarith
    have hexp : Real.exp (β * (r - v)) ≤ r / v := by
      calc Real.exp (β * (r - v)) ≤ Real.exp (Real.log (r / v)) := Real.exp_le_exp.mpr hlog
        _ = r / v := Real.exp_log (div_pos hr hv)
    have e : Real.exp (-(β * v)) = Real.exp (-(β * r)) * Real.exp (β * (r - v)) := by
      rw [← Real.exp_add]; ring_nf
    rw [e]
    have hp := Real.exp_pos (-(β * r))
    rw [le_div_iff₀ hv] at hexp
    nlinarith
  · have ha : 0 < 1 - α := by rcases hα with ⟨_, h2⟩; exact sub_pos.mpr (lt_of_le_of_ne h2 h)
    have hα0 : 0 ≤ α := hα.1
    set a := 1 - α with ha_def
    have ha1 : a ≤ 1 := by linarith
    have hαa : α = 1 - a := by linarith
    set x := r / v with hx
    have hx1 : 1 ≤ x := by rw [hx, le_div_iff₀ hv]; linarith
    have hxpos : 0 < x := by linarith
    set X := x ^ a with hX
    have hXpos : 0 < X := Real.rpow_pos_of_pos hxpos _
    -- Bernoulli on (1/x)^a
    have hbern := rpow_one_add_le_one_add_mul_self (s := 1 / x - 1)
      (by have : 0 < 1 / x := by positivity
          linarith) ha.le ha1
    have e1 : 1 + (1 / x - 1) = x⁻¹ := by ring
    rw [e1, Real.inv_rpow hxpos.le, ← hX] at hbern
    -- hbern : X⁻¹ ≤ 1 + a * (1/x - 1)
    have hX2 : x ≤ X * (α * x + a) := by
      have : X⁻¹ * x ≤ (1 + a * (1 / x - 1)) * x := mul_le_mul_of_nonneg_right hbern hxpos.le
      have e2 : (1 + a * (1 / x - 1)) * x = α * x + a := by
        rw [hαa]; field_simp; ring
      rw [e2] at this
      have e3 : X⁻¹ * x * X = x := by field_simp
      have := mul_le_mul_of_nonneg_right this hXpos.le
      rw [e3] at this; linarith
    set Bv := 1 + a * (β * v) with hBv
    set Br := 1 + a * (β * r) with hBr
    have hBv1 : 1 ≤ Bv := by have : 0 ≤ a * (β * v) := by positivity
                             linarith
    have hBvp : 0 < Bv := by linarith
    have hBrp : 0 < Br := by have : 0 ≤ a * (β * r) := by positivity
                             linarith
    have hrx : r = x * v := by rw [hx]; field_simp
    -- Br * (α x + a) ≤ x * Bv
    have hk : Br * (α * x + a) ≤ x * Bv := by
      have hy : α * (β * v) * x ≤ 1 := by
        have : α * (β * v) * x = α * β * r := by rw [hrx]; ring
        linarith
      have : (x - 1) * (α * (β * v) * x - 1) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
      rw [hBr, hBv, hrx, hαa]
      rw [hαa] at this
      nlinarith
    have hpos2 : 0 < α * x + a := by positivity
    have hk2 : Br ≤ X * Bv := by
      have : Br * (α * x + a) ≤ X * Bv * (α * x + a) := by
        calc Br * (α * x + a) ≤ x * Bv := hk
          _ ≤ X * (α * x + a) * Bv := mul_le_mul_of_nonneg_right hX2 hBvp.le
          _ = X * Bv * (α * x + a) := by ring
      exact le_of_mul_le_mul_right this hpos2
    have hk3 : Br ^ (1 / a) ≤ x * Bv ^ (1 / a) := by
      have := Real.rpow_le_rpow hBrp.le hk2 (by positivity : (0:ℝ) ≤ 1 / a)
      rwa [Real.mul_rpow hXpos.le hBvp.le, hX, ← Real.rpow_mul hxpos.le,
        mul_one_div_cancel ha.ne', Real.rpow_one] at this
    rw [Real.rpow_neg hBvp.le, Real.rpow_neg hBrp.le]
    have p1 : 0 < Bv ^ (1 / a) := Real.rpow_pos_of_pos hBvp _
    have p2 : 0 < Br ^ (1 / a) := Real.rpow_pos_of_pos hBrp _
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_le_div_iff₀ p1 p2]
    rw [hrx]
    nlinarith

theorem solution (α w q r : ℝ) (hα : α ∈ Set.Icc (0 : ℝ) 1) (hw : 0 < w)
    (hq : q ∈ Set.Ioo (0 : ℝ) 1) (hr : r ∈ rSet α w q) :
    r ∈ Set.Ici (0 : ℝ) ∧ IsMaxOn (fun v => v * Fbar α w q r v) (Set.Ici 0) r := by
  have hc := hGAInv_pos α q hα hq
  set c := GammaAInv α q with hc_def
  by_cases hrw : r < w
  · have hrL : rLow α w q ≤ r := by
      rcases hr with h | h
      · exact h.1
      · linarith [h.1]
    have hrL' : w / (c + 1) ≤ r := hrL
    have hr0 : 0 < r := lt_of_lt_of_le (by positivity) hrL'
    refine ⟨hr0.le, ?_⟩
    intro v hv
    simp only [Set.mem_setOf_eq]
    have hfr : r * Fbar α w q r r = r := by
      simp only [Fbar, hrw, if_true, Gbar, lt_irrefl, if_false, hrw.le, sub_self, mul_zero,
        zero_div, hGA_zero, mul_one]
    rw [hfr]
    simp only [Fbar, hrw, if_true, Gbar, div_one, one_mul]
    by_cases hvr : v < r
    · rw [if_pos hvr, hGAInv_one, zero_mul, zero_div, hGA_zero, mul_one]; exact hvr.le
    rw [if_neg hvr]
    by_cases hvw : v ≤ w
    · rw [if_pos hvw]
      have e : c * (v - r) / (w - r) = c / (w - r) * (v - r) := by ring
      rw [e]
      apply lemA α _ r v hα hr0 _ (not_lt.mp hvr)
      have hd : 0 < w - r := by linarith
      rw [div_mul_eq_mul_div, le_div_iff₀ hd]
      rw [div_le_iff₀ (by linarith : (0:ℝ) < c + 1)] at hrL'
      linarith
    · rw [if_neg hvw]; simp [hr0.le]
  · push_neg at hrw
    have hr0 : 0 ≤ r := by linarith
    have hαcr : α * c * r ≤ w := by
      rcases hr with h | h
      · linarith [h.2]
      · exact h.2
    have hF1 : ∀ v, 0 ≤ v → v ≤ r → Fbar α w q r v = GammaA α (c * v / w) := by
      intro v hv0 hvr
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
      rw [if_neg (by linarith), if_pos hvr, div_one, one_mul, sub_zero, sub_zero]
    have hF2 : ∀ v, r < v → Fbar α w q r v = 0 := by
      intro v hv
      simp only [Fbar, not_lt.mpr hrw, if_false, Gbar]
      rw [if_neg (by linarith), if_neg (by linarith)]
    refine ⟨hr0, ?_⟩
    intro v hv
    have hv0 : 0 ≤ v := hv
    simp only [Set.mem_setOf_eq]
    rw [hF1 r hr0 le_rfl]
    have hgr : 0 ≤ r * GammaA α (c * r / w) :=
      mul_nonneg hr0 (hGA_pos α _ hα (by positivity)).le
    by_cases hvr : v ≤ r
    · rw [hF1 v hv0 hvr]
      have e1 : c * v / w = c / w * v := by ring
      have e2 : c * r / w = c / w * r := by ring
      rw [e1, e2]
      apply lemB α _ r v hα (by positivity) _ hv0 hvr
      have : α * (c / w) * r = α * c * r / w := by ring
      rw [this, div_le_one hw]; exact hαcr
    · rw [hF2 v ((not_le.mp hvr))]; simpa using hgr
