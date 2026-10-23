-- Prove2me | solution 1 for YieldPostpone.Interplay.lemma_4_at_cDR2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T04:11:23.713521+00:00
-- url     : https://prove2.me/submissions/21aff05e-c423-4962-9172-c80163768b23

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_eq_5
import Theorems.Thm_YieldPostpone_Interplay_threshold_order


open YieldPostpone.Interplay

namespace YP3L2

/-- optimal ex post revenue with `x` units -/
noncomputable def Rv (P : Params) (x : ℝ) : ℝ :=
  if x ≤ P.a / 2 then x * (P.a - x) / P.b else P.a ^ 2 / (4 * P.b)

lemma Rv_le (P : Params) (x : ℝ) (h : x ≤ P.a / 2) : Rv P x = x * (P.a - x) / P.b := by
  unfold Rv; rw [if_pos h]

lemma Rv_gt (P : Params) (x : ℝ) (h : P.a / 2 < x) : Rv P x = P.a ^ 2 / (4 * P.b) := by
  unfold Rv; rw [if_neg (not_le.mpr h)]

lemma rev_opt (P : Params) (hP : P.Valid) (x : ℝ) (hx : 0 ≤ x) (p : ℝ) (hp : pAdm P p)
    (hopt : ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) :
    salesRev P p x = Rv P x := by
  have hP' := hP
  obtain ⟨ha, hb, _, _, _, _⟩ := hP'
  obtain ⟨hp0, hp1⟩ := hp
  have hd : 0 < demand P p := by
    unfold demand; rw [lt_div_iff₀ hb] at hp1; linarith
  rcases hx.lt_or_eq with hx | hx
  · rcases lt_or_ge x (P.a / 2) with h2 | h2
    · have := ((eq_5 P hP x).1 hx h2 p ⟨hp0, hp1⟩).mp hopt
      rw [Rv_le P x h2.le, this]
      unfold salesRev demand
      have : P.a - P.b * ((P.a - x) / P.b) = x := by field_simp; ring
      rw [this, min_self]; ring
    · have := ((eq_5 P hP x).2 h2 p ⟨hp0, hp1⟩).mp hopt
      rw [this]
      unfold salesRev demand
      have e : P.a - P.b * (P.a / (2 * P.b)) = P.a / 2 := by field_simp; ring
      rw [e, min_eq_left h2]
      rcases h2.lt_or_eq with h3 | h3
      · rw [Rv_gt P x h3]; field_simp; ring
      · rw [← h3, Rv_le P _ le_rfl]; field_simp; ring
  · subst hx
    unfold salesRev
    rw [min_eq_right hd.le, Rv_le P 0 (by linarith)]
    simp

/-- the retailer's expected profit under pay-by-order with optimal ex post pricing -/
noncomputable def Pi (P : Params) (w q : ℝ) : ℝ :=
  P.θ * Rv P q + (1 - P.θ) * Rv P (P.α * q) - w * q

lemma retailerProfit_eq (P : Params) (hP : P.Valid) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w q' p' : ℝ) (hQ : σ.Q w q' = q') (hq : 0 ≤ q') :
    retailerProfit P .OR σ w q' p' = Pi P w q' := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  unfold retailerProfit Pi E
  simp only [delivered, hQ, Scenario.responsive, Scenario.byDelivery, transfer, if_true]
  have h1 : min (1 * q') q' = q' := by simp
  have h2 : min (P.α * q') q' = P.α * q' := min_eq_left (by nlinarith)
  rw [h1, h2]
  have r1 := rev_opt P hP q' hq _ (hpr w q' q' hq).1 (hpr w q' q' hq).2
  have hαq : 0 ≤ P.α * q' := by positivity
  have r2 := rev_opt P hP (P.α * q') hαq _ (hpr w q' (P.α * q') hαq).1 (hpr w q' (P.α * q') hαq).2
  simp only [Bool.false_eq_true, if_false]
  rw [r1, r2]; ring

lemma bRv_le (P : Params) (hb : 0 < P.b) (x : ℝ) (h : x ≤ P.a / 2) : P.b * Rv P x = x * (P.a - x) := by
  rw [Rv_le P x h]; field_simp

lemma bRv_gt (P : Params) (hb : 0 < P.b) (x : ℝ) (h : P.a / 2 < x) : P.b * Rv P x = P.a ^ 2 / 4 := by
  rw [Rv_gt P x h]; field_simp

lemma bPi (P : Params) (w q : ℝ) :
    P.b * Pi P w q = P.θ * (P.b * Rv P q) + (1 - P.θ) * (P.b * Rv P (P.α * q)) - (P.b * w) * q := by
  unfold Pi; ring

/-- region I: no order -/
lemma reg1 (P : Params) (hP : P.Valid) (w : ℝ) (hw : P.a * μ P ≤ P.b * w) (q : ℝ) (hq : 0 < q) :
    Pi P w q < Pi P w 0 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  rw [hμ] at hw
  rw [← mul_lt_mul_iff_of_pos_left hb, bPi, bPi, bRv_le P hb 0 (by linarith), mul_zero,
    bRv_le P hb 0 (by linarith)]
  have hαq : P.α * q < q := by nlinarith
  rcases le_or_gt q (P.a / 2) with h1 | h1
  · rw [bRv_le P hb q h1, bRv_le P hb (P.α * q) (by linarith)]
    nlinarith [mul_pos hθ0 (mul_pos hq hq), mul_pos hθ' (mul_pos (mul_pos hα0 hα0) (mul_pos hq hq)),
      mul_le_mul_of_nonneg_right hw hq.le]
  · rw [bRv_gt P hb q h1]
    rcases le_or_gt (P.α * q) (P.a / 2) with h2 | h2
    · rw [bRv_le P hb (P.α * q) h2]
      nlinarith [mul_pos hθ0 (mul_pos ha (sub_pos.mpr h1)), mul_pos hθ' (mul_pos (mul_pos hα0 hα0) (mul_pos hq hq)),
        mul_le_mul_of_nonneg_right hw hq.le, mul_pos hθ0 ha]
    · rw [bRv_gt P hb (P.α * q) h2]
      have : P.α * q ≤ (P.α * (1 - P.θ) + P.θ) * q := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hw hq.le, mul_le_mul_of_nonneg_left this ha.le]

/-- region II: interior order below a/2 -/
lemma reg2 (P : Params) (hP : P.Valid) (w q0 : ℝ) (hq0 : 0 ≤ q0) (hq0a : q0 ≤ P.a / 2)
    (hw : P.b * w = P.a * μ P - 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * q0) (q : ℝ) (hq : 0 ≤ q) (hne : q ≠ q0) :
    Pi P w q < Pi P w q0 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  rw [hμ] at hw
  have hd : 0 < (q - q0) ^ 2 := by have : q - q0 ≠ 0 := sub_ne_zero.mpr hne; positivity
  rw [← mul_lt_mul_iff_of_pos_left hb, bPi, bPi, hw, bRv_le P hb q0 hq0a,
    bRv_le P hb (P.α * q0) (by nlinarith)]
  rcases le_or_gt q (P.a / 2) with h1 | h1
  · rw [bRv_le P hb q h1, bRv_le P hb (P.α * q) (by nlinarith)]
    nlinarith [mul_pos hθ' (mul_pos (mul_pos hα0 hα0) hd), mul_pos hθ0 hd]
  · rw [bRv_gt P hb q h1]
    have hM1 : (2 * q - P.a) ^ 2 ≤ 4 * (q - q0) ^ 2 := by nlinarith
    rcases le_or_gt (P.α * q) (P.a / 2) with h2 | h2
    · rw [bRv_le P hb (P.α * q) h2]
      nlinarith [mul_pos hθ' (mul_pos (mul_pos hα0 hα0) hd), mul_le_mul_of_nonneg_left hM1 hθ0.le]
    · rw [bRv_gt P hb (P.α * q) h2]
      have hlt : 2 * P.α * q - P.a < 2 * P.α * (q - q0) := by nlinarith
      have hM2 : (2 * P.α * q - P.a) ^ 2 < 4 * P.α ^ 2 * (q - q0) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left hM2 hθ', mul_le_mul_of_nonneg_left hM1 hθ0.le]

/-- region III: inflated order -/
lemma reg3 (P : Params) (hP : P.Valid) (w q0 : ℝ) (hq0a : P.a / 2 < q0) (hq0b : P.α * q0 < P.a / 2)
    (hw : P.b * w = P.a * (P.α * (1 - P.θ)) - 2 * (P.α ^ 2 * (1 - P.θ)) * q0) (q : ℝ) (hq : 0 ≤ q)
    (hne : q ≠ q0) : Pi P w q < Pi P w q0 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hd : 0 < (q - q0) ^ 2 := by have : q - q0 ≠ 0 := sub_ne_zero.mpr hne; positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  rw [← mul_lt_mul_iff_of_pos_left hb, bPi, bPi, hw, bRv_gt P hb q0 hq0a,
    bRv_le P hb (P.α * q0) hq0b.le]
  rcases le_or_gt q (P.a / 2) with h1 | h1
  · rw [bRv_le P hb q h1, bRv_le P hb (P.α * q) (by nlinarith)]
    nlinarith [mul_pos hk hd, mul_nonneg hθ0.le (sq_nonneg (P.a / 2 - q))]
  · rw [bRv_gt P hb q h1]
    rcases le_or_gt (P.α * q) (P.a / 2) with h2 | h2
    · rw [bRv_le P hb (P.α * q) h2]
      nlinarith [mul_pos hk hd]
    · rw [bRv_gt P hb (P.α * q) h2]
      have h3 : 0 < P.α * q - P.a / 2 := by linarith
      have hlt : P.α * q - P.a / 2 < P.α * (q - q0) := by nlinarith
      have hM2 : (P.α * q - P.a / 2) ^ 2 < P.α ^ 2 * (q - q0) ^ 2 := by nlinarith
      nlinarith [mul_lt_mul_of_pos_left hM2 hθ']

/-- the retailer's best response under OR -/
noncomputable def qs (P : Params) (w : ℝ) : ℝ :=
  if P.a * μ P ≤ P.b * w then 0
  else if P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w then
    (P.a * μ P - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))
  else (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ)))

lemma br (P : Params) (hP : P.Valid) (w : ℝ) (hw : 0 < w) :
    0 ≤ qs P w ∧ ∀ q : ℝ, 0 ≤ q → q ≠ qs P w → Pi P w q < Pi P w (qs P w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  unfold qs
  split_ifs with h1 h2
  · refine ⟨le_rfl, fun q hq hne => reg1 P hP w h1 q (lt_of_le_of_ne hq (Ne.symm hne))⟩
  · push Not at h1
    refine ⟨div_nonneg (by linarith) (by positivity), fun q hq hne => reg2 P hP w _ (div_nonneg (by linarith) (by positivity)) ?_ ?_ q hq hne⟩
    · rw [div_le_iff₀ (by positivity)]; nlinarith
    · field_simp; ring
  · push Not at h1 h2
    rw [hμ] at h2
    have hq0a : P.a / 2 < (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ))) := by
      rw [lt_div_iff₀ (by positivity)]; nlinarith
    refine ⟨by linarith, fun q hq hne => reg3 P hP w _ hq0a ?_ ?_ q hq hne⟩
    · rw [← mul_div_assoc, div_lt_iff₀ (by positivity)]
      nlinarith [mul_pos hα0 (mul_pos hb hw)]
    · field_simp; ring

lemma qs_reg1 (P : Params) (w : ℝ) (h1 : P.a * μ P ≤ P.b * w) : qs P w = 0 := by
  unfold qs; rw [if_pos h1]

lemma qs_reg2 (P : Params) (w : ℝ) (h1 : P.b * w < P.a * μ P)
    (h2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w) :
    qs P w = (P.a * μ P - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  unfold qs; rw [if_neg (not_le.mpr h1), if_pos h2]

lemma qs_reg3 (P : Params) (w : ℝ) (h1 : P.b * w < P.a * μ P)
    (h2 : P.b * w < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) :
    qs P w = (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ))) := by
  unfold qs; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]

/-- the supplier's value of posting `w` (pay-by-order, retailer best-responds) -/
noncomputable def Vf (P : Params) (c w : ℝ) : ℝ := (w - c) * qs P w

lemma rho_facts (P : Params) (hP : P.Valid) :
    (1 - P.θ) * Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ ∧
    P.α < Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) ∧
    P.α * (1 - P.θ) * Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) < P.α ^ 2 * (1 - P.θ) + P.θ := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hnn : 0 ≤ P.α ^ 2 + P.θ / (1 - P.θ) := by positivity
  have h2 := Real.sq_sqrt hnn
  set ρ := Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ))
  have e1 : (1 - P.θ) * ρ ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := by rw [h2]; field_simp
  refine ⟨e1, ?_, ?_⟩
  · rw [Real.lt_sqrt hα0.le]; have : 0 < P.θ / (1 - P.θ) := div_pos hθ0 hθ'; linarith
  · have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hsq : (P.α * (1 - P.θ) * ρ) ^ 2 < (P.α ^ 2 * (1 - P.θ) + P.θ) ^ 2 := by
      have : (P.α * (1 - P.θ) * ρ) ^ 2 = P.α ^ 2 * (1 - P.θ) * ((1 - P.θ) * ρ ^ 2) := by ring
      rw [this, e1]; nlinarith [mul_pos (mul_pos hα0 hα0) (mul_pos hθ' hθ0), mul_pos hθ0 hθ0]
    exact lt_of_le_of_lt (le_abs_self _) (abs_lt_of_sq_lt_sq hsq (by positivity))

lemma cOR_mul (P : Params) (hP : P.Valid) :
    P.b * cOR P = P.a * (P.α * (1 - P.θ)) * ((1 - P.α) - Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ))) := by
  obtain ⟨ha, hb, _, _, _, _⟩ := hP
  unfold cOR; field_simp

/-- comparison of the two regional maxima: `c ≥ c^OR` favours the non-inflated order -/
lemma keyII (P : Params) (hP : P.Valid) (c : ℝ) (hc : cOR P ≤ c)
    (h0 : 0 ≤ P.a * (P.α * (1 - P.θ)) - P.b * c) :
    (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)
      ≤ (P.a * μ P - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ)) ∧
    (cOR P < c → (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)
      < (P.a * μ P - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ))) := by
  obtain ⟨e1, hρα, _⟩ := rho_facts P hP
  have hm := cOR_mul P hP
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  set ρ := Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ))
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  -- G = (aμ - bc) α - (au - bc) ρ ≥ 0
  have hid : (P.a * μ P - P.b * c) * P.α - (P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ
      = (P.b * c - P.b * cOR P) * (ρ - P.α) := by
    rw [hm, hμ]
    have : P.a * P.α * ((1 - P.θ) * ρ ^ 2) = P.a * P.α * (P.α ^ 2 * (1 - P.θ) + P.θ) := by rw [e1]
    linear_combination (-1 : ℝ) * this
  have hG : 0 ≤ (P.a * μ P - P.b * c) * P.α - (P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ := by
    rw [hid]; apply mul_nonneg _ (by linarith); nlinarith
  have hsq : ∀ L R : ℝ, 0 ≤ L → L ≤ R → L ^ 2 ≤ R ^ 2 := fun L R h1 h2 => by nlinarith
  have hsq' : ∀ L R : ℝ, 0 ≤ L → L < R → L ^ 2 < R ^ 2 := fun L R h1 h2 => by nlinarith
  have e2 : ((P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ) ^ 2 * (1 - P.θ)
      = (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by
    rw [← e1]; ring
  have e3 : ((P.a * μ P - P.b * c) * P.α) ^ 2 * (1 - P.θ)
      = (P.a * μ P - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ)) := by ring
  constructor
  · have := hsq ((P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ) ((P.a * μ P - P.b * c) * P.α) (mul_nonneg h0 hρ0) (by linarith)
    rw [← e2, ← e3]; exact mul_le_mul_of_nonneg_right this hθ'.le
  · intro hlt
    have hG' : 0 < (P.a * μ P - P.b * c) * P.α - (P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ := by
      rw [hid]; apply mul_pos _ (by linarith); nlinarith
    have := hsq' ((P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ) ((P.a * μ P - P.b * c) * P.α) (mul_nonneg h0 hρ0) (by linarith)
    rw [← e2, ← e3]; exact mul_lt_mul_of_pos_right this hθ'

/-- comparison of the two regional maxima: `c < c^OR` favours the inflated order -/
lemma keyIII (P : Params) (hP : P.Valid) (c : ℝ) (hc : c < cOR P)
    (h0 : 0 ≤ P.a * μ P - P.b * c) :
    (P.a * μ P - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ))
      < (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by
  obtain ⟨e1, hρα, _⟩ := rho_facts P hP
  have hm := cOR_mul P hP
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  set ρ := Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ))
  have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
  have hid : (P.a * μ P - P.b * c) * P.α - (P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ
      = (P.b * c - P.b * cOR P) * (ρ - P.α) := by
    rw [hm, hμ]
    have : P.a * P.α * ((1 - P.θ) * ρ ^ 2) = P.a * P.α * (P.α ^ 2 * (1 - P.θ) + P.θ) := by rw [e1]
    linear_combination (-1 : ℝ) * this
  have hG : (P.a * μ P - P.b * c) * P.α < (P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ := by
    have : (P.b * c - P.b * cOR P) * (ρ - P.α) < 0 := mul_neg_of_neg_of_pos (by nlinarith) (by linarith)
    linarith
  have hL : 0 ≤ (P.a * μ P - P.b * c) * P.α := mul_nonneg h0 hα0.le
  have := pow_lt_pow_left₀ hG hL (by norm_num : (2:ℕ) ≠ 0)
  have e2 : ((P.a * (P.α * (1 - P.θ)) - P.b * c) * ρ) ^ 2 * (1 - P.θ)
      = (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by
    rw [← e1]; ring
  have e3 : ((P.a * μ P - P.b * c) * P.α) ^ 2 * (1 - P.θ)
      = (P.a * μ P - P.b * c) ^ 2 * (P.α ^ 2 * (1 - P.θ)) := by ring
  rw [← e2, ← e3]; exact mul_lt_mul_of_pos_right this hθ'

lemma Vf_reg1 (P : Params) (c w : ℝ) (h1 : P.a * μ P ≤ P.b * w) : Vf P c w = 0 := by
  unfold Vf; rw [qs_reg1 P w h1, mul_zero]

lemma Vf_reg2 (P : Params) (c w : ℝ) (h1 : P.b * w < P.a * μ P)
    (h2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w) :
    Vf P c w = (w - c) * (P.a * μ P - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  unfold Vf; rw [qs_reg2 P w h1 h2]; ring

lemma Vf_reg3 (P : Params) (c w : ℝ) (h2 : P.b * w < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)))
    (hP : P.Valid) :
    Vf P c w = (w - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ))) := by
  have h1 : P.b * w < P.a * μ P := by
    obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
    have : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by nlinarith
    nlinarith
  unfold Vf; rw [qs_reg3 P w h1 h2]; ring

/-- supplier optimum without order inflation (`c ≥ c^OR`) -/
lemma sup2 (P : Params) (hP : P.Valid) (c : ℝ) (hc0 : 0 < c) (hcμ : P.b * c < P.a * μ P)
    (hcOR : cOR P ≤ c) (w2 : ℝ) (hw2 : w2 = (P.a * μ P + P.b * c) / (2 * P.b)) :
    c < w2 ∧ w2 < P.a / P.b ∧
    P.b * w2 < P.a * μ P ∧ P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w2 ∧
    qs P w2 = (P.a * μ P - P.b * c) / (4 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    Vf P c w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    ∀ w : ℝ, c < w → w < P.a / P.b →
      Vf P c w ≤ Vf P c w2 ∧ (cOR P < c → w ≠ w2 → Vf P c w < Vf P c w2) := by
  obtain ⟨e1, hρα, huρ⟩ := rho_facts P hP
  have hm := cOR_mul P hP
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  have hμ1 : μ P < 1 := by rw [hμ]; nlinarith
  have hbw2 : P.b * w2 = (P.a * μ P + P.b * c) / 2 := by rw [hw2]; field_simp
  have hbc : P.b * cOR P ≤ P.b * c := mul_le_mul_of_nonneg_left hcOR hb.le
  have hcw : c < w2 := by
    have : P.b * c < P.b * w2 := by rw [hbw2]; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hwa : w2 < P.a / P.b := by
    rw [lt_div_iff₀ hb, mul_comm, hbw2]
    have := mul_lt_mul_of_pos_left hμ1 ha
    linarith
  have hr1 : P.b * w2 < P.a * μ P := by rw [hbw2]; linarith
  have hr2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w2 := by
    rw [hbw2, hμ]; rw [hm] at hbc
    nlinarith [mul_lt_mul_of_pos_left huρ ha]
  have hq : qs P w2 = (P.a * μ P - P.b * c) / (4 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    rw [qs_reg2 P w2 hr1 hr2, hbw2]; field_simp; ring
  have hwc : w2 - c = (P.a * μ P - P.b * c) / (2 * P.b) := by rw [hw2]; field_simp; ring
  have hV2 : Vf P c w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    unfold Vf; rw [hq, hwc]; field_simp; ring
  refine ⟨hcw, hwa, hr1, hr2, hq, hV2, ?_⟩
  intro w hw1 hw2'
  have hVpos : 0 < Vf P c w2 := by
    rw [hV2]; have : 0 < P.a * μ P - P.b * c := by linarith
    positivity
  by_cases h1 : P.a * μ P ≤ P.b * w
  · rw [Vf_reg1 P c w h1]; exact ⟨hVpos.le, fun _ _ => hVpos⟩
  push Not at h1
  by_cases h2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w
  · rw [Vf_reg2 P c w h1 h2, Vf_reg2 P c w2 hr1 hr2]
    have h3 : P.b * w2 * 2 = P.a * μ P + P.b * c := by rw [hbw2]; ring
    have hid : (w2 - c) * (P.a * μ P - P.b * w2) - (w - c) * (P.a * μ P - P.b * w) = P.b * (w - w2) ^ 2 := by
      linear_combination (w - w2) * h3
    constructor
    · apply div_le_div_of_nonneg_right _ (by positivity)
      rw [← sub_nonneg, hid]; positivity
    · intro _ hne
      apply div_lt_div_of_pos_right _ (by positivity)
      have : 0 < (w - w2) ^ 2 := by have := sub_ne_zero.mpr hne; positivity
      rw [← sub_pos, hid]; positivity
  · push Not at h2
    rw [Vf_reg3 P c w h2 hP, hV2]
    have hA : 4 * P.b * ((w - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w))
        ≤ (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 := by
      have : (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 - 4 * P.b * ((w - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w))
          = (P.a * (P.α * (1 - P.θ)) + P.b * c - 2 * P.b * w) ^ 2 := by ring
      rw [← sub_nonneg, this]; positivity
    rcases lt_or_ge (P.a * (P.α * (1 - P.θ)) - P.b * c) 0 with hneg | hnn
    · have hl : (w - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ))) < 0 := by
        apply div_neg_of_neg_of_pos _ (by positivity)
        apply mul_neg_of_pos_of_neg (by linarith)
        have : P.b * c < P.b * w := mul_lt_mul_of_pos_left hw1 hb
        linarith
      rw [hV2] at hVpos
      exact ⟨by linarith, fun _ _ => by linarith⟩
    · obtain ⟨kle, klt⟩ := keyII P hP c hcOR hnn
      have hA' := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))
      rw [div_le_div_iff₀ (by positivity) (by positivity), div_lt_div_iff₀ (by positivity) (by positivity)]
      constructor
      · linear_combination hA' + 2 * kle
      · intro hlt _
        linear_combination hA' + 2 * klt hlt

/-- supplier optimum with order inflation (`c < c^OR`) -/
lemma sup3 (P : Params) (hP : P.Valid) (c : ℝ) (hc0 : 0 < c) (hcμ : P.b * c < P.a * μ P)
    (hcOR : c < cOR P) (w3 : ℝ) (hw3 : w3 = (P.a * (P.α * (1 - P.θ)) + P.b * c) / (2 * P.b)) :
    c < w3 ∧ w3 < P.a / P.b ∧
    P.b * w3 < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    qs P w3 = (P.a * (P.α * (1 - P.θ)) - P.b * c) / (4 * (P.α ^ 2 * (1 - P.θ))) ∧
    Vf P c w3 = (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ))) ∧
    ∀ w : ℝ, c < w → w < P.a / P.b → w ≠ w3 → Vf P c w < Vf P c w3 := by
  obtain ⟨e1, hρα, huρ⟩ := rho_facts P hP
  have hm := cOR_mul P hP
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  have hu1 : P.α * (1 - P.θ) < 1 := by nlinarith
  have hbw3 : P.b * w3 = (P.a * (P.α * (1 - P.θ)) + P.b * c) / 2 := by rw [hw3]; field_simp
  have hbc : P.b * c < P.b * cOR P := mul_lt_mul_of_pos_left hcOR hb
  rw [hm] at hbc
  have huρ' : P.α * (1 - P.θ) * P.α < P.α * (1 - P.θ) * Real.sqrt (P.α ^ 2 + P.θ / (1 - P.θ)) :=
    mul_lt_mul_of_pos_left hρα (by positivity)
  have hpos : 0 < P.a * (P.α * (1 - P.θ)) - P.b * c := by
    have := mul_lt_mul_of_pos_left huρ' ha
    nlinarith [mul_pos ha (mul_pos (mul_pos hα0 hθ') hα0)]
  have hcw : c < w3 := by
    have : P.b * c < P.b * w3 := by rw [hbw3]; linarith
    exact lt_of_mul_lt_mul_left this hb.le
  have hwa : w3 < P.a / P.b := by
    rw [lt_div_iff₀ hb, mul_comm, hbw3]
    have := mul_lt_mul_of_pos_left hu1 ha
    linarith
  have hr3 : P.b * w3 < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    rw [hbw3, hμ]; nlinarith [mul_lt_mul_of_pos_left huρ' ha]
  have hr1 : P.b * w3 < P.a * μ P := by
    have : 0 < P.a * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
    have : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) = P.a * μ P - P.a * (P.α ^ 2 * (1 - P.θ) + P.θ) := by ring
    linarith
  have hq : qs P w3 = (P.a * (P.α * (1 - P.θ)) - P.b * c) / (4 * (P.α ^ 2 * (1 - P.θ))) := by
    rw [qs_reg3 P w3 hr1 hr3, hbw3]; field_simp; ring
  have hwc : w3 - c = (P.a * (P.α * (1 - P.θ)) - P.b * c) / (2 * P.b) := by rw [hw3]; field_simp; ring
  have hV3 : Vf P c w3 = (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ))) := by
    unfold Vf; rw [hq, hwc]; field_simp; ring
  refine ⟨hcw, hwa, hr3, hq, hV3, ?_⟩
  intro w hw1 hw2 hne
  have hVpos : 0 < Vf P c w3 := by rw [hV3]; positivity
  by_cases h1 : P.a * μ P ≤ P.b * w
  · rw [Vf_reg1 P c w h1]; exact hVpos
  push Not at h1
  by_cases h2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w
  · rw [Vf_reg2 P c w h1 h2, hV3]
    have hA : 4 * P.b * ((w - c) * (P.a * μ P - P.b * w)) ≤ (P.a * μ P - P.b * c) ^ 2 := by
      have : (P.a * μ P - P.b * c) ^ 2 - 4 * P.b * ((w - c) * (P.a * μ P - P.b * w))
          = (P.a * μ P + P.b * c - 2 * P.b * w) ^ 2 := by ring
      rw [← sub_nonneg, this]; positivity
    have kl := keyIII P hP c hcOR (by linarith)
    have hA' := mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 2 * (P.α ^ 2 * (1 - P.θ)))
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    linear_combination hA' + 2 * kl
  · push Not at h2
    rw [Vf_reg3 P c w h2 hP, Vf_reg3 P c w3 hr3 hP]
    apply div_lt_div_of_pos_right _ (by positivity)
    have : 0 < (w - w3) ^ 2 := by have := sub_ne_zero.mpr hne; positivity
    have h3 : P.b * w3 * 2 = P.a * (P.α * (1 - P.θ)) + P.b * c := by rw [hbw3]; ring
    have hid : (w3 - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w3) - (w - c) * (P.a * (P.α * (1 - P.θ)) - P.b * w)
        = P.b * (w - w3) ^ 2 := by
      linear_combination (w - w3) * h3
    rw [← sub_pos, hid]; positivity

end YP3L2


open YieldPostpone.Interplay

namespace YP3L2

lemma surplus_eval (P : Params) (hb : 0 < P.b) (p X : ℝ) :
    surplus P p X = (P.a / P.b - p) * min (demand P p) X - (min (demand P p) X) ^ 2 / (2 * P.b) := by
  unfold surplus
  have e : (fun t : ℝ => (P.a - t) / P.b - p) = fun t => (P.a / P.b - p) - t / P.b := by
    funext t; ring
  rw [e, intervalIntegral.integral_sub intervalIntegrable_const
    (Continuous.intervalIntegrable (by fun_prop : Continuous fun t : ℝ => t / P.b) _ _)]
  simp [intervalIntegral.integral_div, integral_id]
  ring

noncomputable def Sv (P : Params) (x : ℝ) : ℝ :=
  if x ≤ P.a / 2 then x ^ 2 / (2 * P.b) else P.a ^ 2 / (8 * P.b)

lemma surplus_opt (P : Params) (hP : P.Valid) (x : ℝ) (hx : 0 < x) (p : ℝ) (hp : pAdm P p)
    (hopt : ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) :
    surplus P p x = Sv P x := by
  have hP' := hP
  obtain ⟨ha, hb, _, _, _, _⟩ := hP'
  rw [surplus_eval P hb]
  rcases lt_or_ge x (P.a / 2) with h2 | h2
  · have := ((eq_5 P hP x).1 hx h2 p hp).mp hopt
    subst this
    have hd : demand P ((P.a - x) / P.b) = x := by unfold demand; field_simp; ring
    unfold Sv; rw [hd, min_self, if_pos h2.le]; field_simp; ring
  · have := ((eq_5 P hP x).2 h2 p hp).mp hopt
    subst this
    have hd : demand P (P.a / (2 * P.b)) = P.a / 2 := by unfold demand; field_simp; ring
    rw [hd, min_eq_left h2]
    unfold Sv
    split_ifs with h3
    · have : x = P.a / 2 := le_antisymm h3 h2
      subst this; field_simp; ring
    · field_simp; ring

lemma wAdm_OR (P : Params) (c w : ℝ) : wAdm P c .OR w ↔ c < w ∧ w < P.a / P.b := by
  unfold wAdm; simp [Scenario.byDelivery]

/-- consequences of subgame perfection in scenario OR -/
lemma spe_facts (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (h : IsSPE P c .OR σ) :
    (∀ w q : ℝ, c < w → w < P.a / P.b → 0 ≤ q → σ.Q w q = q) ∧
    (∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x) ∧
    (∀ w : ℝ, c < w → w < P.a / P.b → σ.q w = qs P w) ∧
    c < σ.w ∧ σ.w < P.a / P.b ∧
    (∀ w : ℝ, c < w → w < P.a / P.b → Vf P c w ≤ Vf P c σ.w) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hQ : ∀ w q : ℝ, c < w → w < P.a / P.b → 0 ≤ q → σ.Q w q = q := fun w q hw1 hw2 hq =>
    (h1 w q ((wAdm_OR P c w).mpr ⟨hw1, hw2⟩) hq).2 rfl
  have hpr := h2 rfl
  have hq : ∀ w : ℝ, c < w → w < P.a / P.b → σ.q w = qs P w := by
    intro w hw1 hw2
    obtain ⟨hq0, _, hopt⟩ := h3 w ((wAdm_OR P c w).mpr ⟨hw1, hw2⟩)
    have hw0 : 0 < w := by linarith
    obtain ⟨hqs0, hlt⟩ := br P hP w hw0
    by_contra hne
    have e1 := hopt (qs P w) (σ.p w) hqs0 (fun h => absurd h (by decide))
    rw [retailerProfit_eq P hP σ hpr w _ _ (hQ w _ hw1 hw2 hqs0) hqs0,
      retailerProfit_eq P hP σ hpr w _ _ (hQ w _ hw1 hw2 hq0) hq0] at e1
    have := hlt (σ.q w) hq0 hne
    linarith
  have hV : ∀ w : ℝ, c < w → w < P.a / P.b → supplierValue P c .OR σ w = Vf P c w := by
    intro w hw1 hw2
    unfold supplierValue supplierProfit E transfer Vf
    have hqs0 := (br P hP w (by linarith)).1
    rw [hq w hw1 hw2, hQ w _ hw1 hw2 hqs0]
    simp [Scenario.byDelivery]
    ring
  obtain ⟨hwa, hopt⟩ := h4
  obtain ⟨hw1, hw2⟩ := (wAdm_OR P c σ.w).mp hwa
  refine ⟨hQ, hpr, hq, hw1, hw2, ?_⟩
  intro w hw1' hw2'
  have := hopt w ((wAdm_OR P c w).mpr ⟨hw1', hw2'⟩)
  rwa [hV w hw1' hw2', hV σ.w hw1 hw2] at this

end YP3L2


open YieldPostpone.Interplay

namespace YP3L2

noncomputable def prf (P : Params) (x : ℝ) : ℝ :=
  if 0 < x ∧ x < P.a / 2 then (P.a - x) / P.b else P.a / (2 * P.b)

lemma prf_opt (P : Params) (hP : P.Valid) (x : ℝ) (hx : 0 ≤ x) :
    pAdm P (prf P x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (prf P x) x := by
  have hP' := hP
  obtain ⟨ha, hb, _, _, _, _⟩ := hP'
  have hadm2 : pAdm P (P.a / (2 * P.b)) := by
    constructor
    · positivity
    · rw [div_lt_div_iff₀ (by positivity) hb]; nlinarith
  unfold prf
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    have hadm : pAdm P ((P.a - x) / P.b) := by
      constructor
      · apply div_pos _ hb; linarith
      · rw [div_lt_div_iff₀ hb hb]; nlinarith
    exact ⟨hadm, ((eq_5 P hP x).1 h1 h2 _ hadm).mpr rfl⟩
  · refine ⟨hadm2, ?_⟩
    rcases hx.lt_or_eq with hx | hx
    · have h2 : P.a / 2 ≤ x := by
        by_contra hc; push Not at hc; exact h ⟨hx, hc⟩
      exact ((eq_5 P hP x).2 h2 _ hadm2).mpr rfl
    · subst hx
      intro p' hp'
      have hz : ∀ p, pAdm P p → salesRev P p 0 = 0 := by
        intro p hp
        obtain ⟨_, hp1⟩ := hp
        unfold salesRev demand
        rw [lt_div_iff₀ hb] at hp1
        rw [min_eq_right (by linarith)]; ring
      rw [hz p' hp', hz _ hadm2]

lemma supplierValue_eq (P : Params) (c : ℝ) (σ : Profile) (hQ : ∀ w q, σ.Q w q = q) (w : ℝ) :
    supplierValue P c .OR σ w = (w - c) * σ.q w := by
  unfold supplierValue supplierProfit E transfer
  rw [hQ]
  simp [Scenario.byDelivery]
  ring

end YP3L2


open YieldPostpone.Interplay

namespace YP3DA

lemma sp_eq (P : Params) (c w Q q : ℝ) :
    supplierProfit P c .DA w Q q =
      P.θ * (w * min Q q) + (1 - P.θ) * (w * min (P.α * Q) q) - c * Q := by
  simp [supplierProfit, E, transfer, delivered, Scenario.byDelivery]

lemma rp_eq (P : Params) (σ : Profile) (w q p : ℝ) :
    retailerProfit P .DA σ w q p =
      P.θ * (p * min (P.a - P.b * p) (min (σ.Q w q) q) - w * min (σ.Q w q) q) +
      (1 - P.θ) * (p * min (P.a - P.b * p) (min (P.α * σ.Q w q) q) -
        w * min (P.α * σ.Q w q) q) := by
  simp [retailerProfit, E, transfer, delivered, salesRev, demand, Scenario.byDelivery,
    Scenario.responsive]

lemma surplus_eq (P : Params) (hb : 0 < P.b) (p X : ℝ) :
    surplus P p X = min (P.a - P.b * p) X * (P.a / P.b - p) -
      (min (P.a - P.b * p) X) ^ 2 / (2 * P.b) := by
  unfold surplus demand
  set m := min (P.a - P.b * p) X
  have hb0 : P.b ≠ 0 := hb.ne'
  have : ∀ t ∈ Set.uIcc (0:ℝ) m, HasDerivAt (fun t => t * (P.a / P.b - p) - t ^ 2 / (2 * P.b))
      ((P.a - t) / P.b - p) t := by
    intro t _
    have h1 := ((hasDerivAt_id t).mul_const (P.a / P.b - p))
    have h2 := ((hasDerivAt_pow 2 t).div_const (2 * P.b))
    refine (h1.sub h2).congr_deriv ?_
    simp only [id, Nat.cast_ofNat]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt this]
  · ring
  · apply Continuous.intervalIntegrable
    fun_prop


/-- Production: low regime, `q` is optimal. -/
lemma prod_low (α θ c w q Q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : 0 < c) (hw : c < w * (α * (1 - θ) + θ)) (hlow : α * (1 - θ) * w ≤ c) (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q ≤
      θ * (w * min q q) + (1 - θ) * (w * min (α * q) q) - c * q := by
  have h1θ : 0 < 1 - θ := by linarith
  have hαq : α * q ≤ q := by nlinarith
  rw [min_self, min_eq_left hαq]
  rcases le_total Q q with h | h
  · have hαQ : α * Q ≤ q := by nlinarith
    rw [min_eq_left h, min_eq_left hαQ]
    have : 0 ≤ (w * (α * (1 - θ) + θ) - c) * (q - Q) := by
      apply mul_nonneg <;> linarith
    nlinarith
  · rw [min_eq_right h]
    have hm1 : min (α * Q) q ≤ α * Q := min_le_left _ _
    have hw0 : 0 ≤ w := by
      by_contra hneg
      push Not at hneg
      have : w * (α * (1 - θ) + θ) < 0 := mul_neg_of_neg_of_pos hneg (by positivity)
      linarith
    have h2 : (1 - θ) * (w * min (α * Q) q) ≤ (1 - θ) * (w * (α * Q)) := by
      apply mul_le_mul_of_nonneg_left _ h1θ.le
      exact mul_le_mul_of_nonneg_left hm1 hw0
    have h3 : 0 ≤ (c - α * (1 - θ) * w) * (Q - q) := by
      apply mul_nonneg <;> linarith
    nlinarith

/-- Production: high regime, `q/α` is the unique optimum. -/
lemma prod_high (α θ c w q Q : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc : 0 < c) (hw : c < w * (α * (1 - θ) + θ)) (hhigh : c < α * (1 - θ) * w)
    (hq : 0 ≤ q) (hQ : 0 ≤ Q) :
    θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q ≤
      θ * (w * min (q / α) q) + (1 - θ) * (w * min (α * (q / α)) q) - c * (q / α) ∧
    (θ * (w * min Q q) + (1 - θ) * (w * min (α * Q) q) - c * Q =
      θ * (w * min (q / α) q) + (1 - θ) * (w * min (α * (q / α)) q) - c * (q / α) →
      Q = q / α) := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hqα : q ≤ q / α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαqα : α * (q / α) = q := by field_simp
  rw [min_eq_right hqα, hαqα, min_self]
  have hw0 : 0 < w := by
    by_contra hneg
    push Not at hneg
    have : α * (1 - θ) * w ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hneg
    linarith
  have hk : 0 < α * (1 - θ) * w - c := by linarith
  have hk2 : 0 < w * (α * (1 - θ) + θ) - c := by linarith
  rcases le_total Q q with h | h
  · have hαQ : α * Q ≤ q := by nlinarith
    rw [min_eq_left h, min_eq_left hαQ]
    -- S(q/α) - S(Q) = (wμ-c)(q-Q) + q(1-α)(α(1-θ)w - c)/α
    have key : (θ * (w * q) + (1 - θ) * (w * q) - c * (q / α)) -
        (θ * (w * Q) + (1 - θ) * (w * (α * Q)) - c * Q) =
        (w * (α * (1 - θ) + θ) - c) * (q - Q) + q * (1 - α) * (α * (1 - θ) * w - c) / α := by
      field_simp; ring
    have t1 : 0 ≤ (w * (α * (1 - θ) + θ) - c) * (q - Q) := by
      apply mul_nonneg <;> linarith
    have t2 : 0 ≤ q * (1 - α) * (α * (1 - θ) * w - c) / α := by positivity
    refine ⟨by linarith, fun heq => ?_⟩
    have z1 : (w * (α * (1 - θ) + θ) - c) * (q - Q) = 0 := by linarith
    have z2 : q * (1 - α) * (α * (1 - θ) * w - c) / α = 0 := by linarith
    have hqQ : q - Q = 0 := by
      rcases mul_eq_zero.mp z1 with h' | h'
      · linarith
      · exact h'
    have hq0 : q = 0 := by
      have : q * (1 - α) * (α * (1 - θ) * w - c) = 0 := by
        rw [div_eq_zero_iff] at z2
        rcases z2 with h' | h'
        · exact h'
        · linarith
      rcases mul_eq_zero.mp this with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact h''
        · linarith
      · linarith
    rw [hq0, zero_div]; linarith
  · rw [min_eq_right h]
    rcases le_total Q (q / α) with h' | h'
    · have hαQ : α * Q ≤ q := by
        have := mul_le_mul_of_nonneg_left h' hα0.le
        rwa [hαqα] at this
      rw [min_eq_left hαQ]
      have key : (θ * (w * q) + (1 - θ) * (w * q) - c * (q / α)) -
          (θ * (w * q) + (1 - θ) * (w * (α * Q)) - c * Q) =
          (α * (1 - θ) * w - c) * (q / α - Q) := by
        field_simp; ring
      have t1 : 0 ≤ (α * (1 - θ) * w - c) * (q / α - Q) := by
        apply mul_nonneg <;> linarith
      refine ⟨by linarith, fun heq => ?_⟩
      have z : (α * (1 - θ) * w - c) * (q / α - Q) = 0 := by linarith
      rcases mul_eq_zero.mp z with h'' | h''
      · linarith
      · linarith
    · have hαQ : q ≤ α * Q := by
        have := mul_le_mul_of_nonneg_left h' hα0.le
        rwa [hαqα] at this
      rw [min_eq_right hαQ]
      refine ⟨by nlinarith, fun heq => ?_⟩
      have : c * (Q - q / α) = 0 := by linarith
      rcases mul_eq_zero.mp this with h'' | h''
      · linarith
      · linarith

end YP3DA


namespace YP3DR

/-! Pure real-algebra facts for the DR scenario. Throughout
`u = α(1-θ)`, `μ = α(1-θ)+θ`, `σ₂ = α²(1-θ)+θ`. -/

/-- `d * Q(c) = T² - M²` form of the comparison `G3 - G0`. -/
lemma G3_sub_G0 (a b α θ c S : ℝ) (hb : 0 < b) (hα0 : 0 < α) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hS : S ^ 2 = α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) :
    (b * c - a * α) ^ 2 / (8 * b * α ^ 2) -
      (α * (1 - θ) + θ) * θ * c * (a * α * (1 - θ) - b * c) /
        (2 * α ^ 2 * (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ)) =
      ((( α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b * c -
          a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ)) ^ 2 -
        (2 * a * α * (1 - θ) * θ * S) ^ 2) /
      (8 * b * α ^ 2 * (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hs2 : 0 < α ^ 2 * (1 - θ) + θ := by positivity
  have hd : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by positivity
  have e : (2 * a * α * (1 - θ) * θ * S) ^ 2 =
      4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) := by
    rw [← hS]; ring
  rw [e]
  field_simp
  ring

/-- `T(c₂)² - M² < 0`, the key polynomial fact at `c = c^DR_2`. -/
lemma T_c2 (a b α θ S : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : 0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ)
    (hS : S ^ 2 = α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) :
    ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b *
          (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) -
        a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ)) ^ 2 -
      (2 * a * α * (1 - θ) * θ * S) ^ 2 < 0 := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hm : 0 < (α * (1 - θ) + θ) + θ := by positivity
  have e : (2 * a * α * (1 - θ) * θ * S) ^ 2 =
      4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) := by
    rw [← hS]; ring
  rw [e]
  have e2 : (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) * b *
          (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) -
        a * α * (1 - θ) * ((α * (1 - θ) + θ) ^ 2 + θ) =
      a * α * (1 - θ) * ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α * (1 - θ) + θ) - ((α * (1 - θ) + θ) ^ 2 + θ) * ((α * (1 - θ) + θ) + θ)) /
        ((α * (1 - θ) + θ) + θ) := by
    field_simp
  rw [e2, div_pow, sub_neg, div_lt_iff₀ (by positivity)]
  have hd : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by positivity
  have key : 4 * a ^ 2 * α ^ 2 * (1 - θ) ^ 2 * θ ^ 2 * (α * (α * (1 - θ) + θ) * (1 - α) * (1 - θ)) *
        ((α * (1 - θ) + θ) + θ) ^ 2 -
      (a * α * (1 - θ) * ((α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α * (1 - θ) + θ) - ((α * (1 - θ) + θ) ^ 2 + θ) * ((α * (1 - θ) + θ) + θ))) ^ 2 =
      a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) ^ 3 *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by
    ring
  have : 0 < a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) ^ 3 *
        (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) := by positivity
  linarith

lemma K_pos (α θ : ℝ) (h1 : 9 / 16 ≤ α) (h2 : α < 1) (h3 : 0 < θ) (h4 : θ < 1) :
    0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ := by
  have ha : 0 < α := by linarith
  have hθ' : 0 < 1 - θ := by linarith
  nlinarith [mul_pos ha h3, mul_pos (mul_pos ha ha) hθ', mul_pos (mul_pos ha h3) hθ', mul_pos h3 hθ',
    mul_pos (mul_pos ha ha) h3, mul_pos (mul_pos (mul_pos ha ha) ha) (mul_pos hθ' hθ')]

/-- Case C comparison at `c₂`: `σ₂ (aα - b c₂)² < α² (aμ - b c₂)²`. -/
lemma caseC_c2 (a b α θ : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hK : 0 < α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) :
    (α ^ 2 * (1 - θ) + θ) *
        (a * α - b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ)))) ^ 2 <
      α ^ 2 * (a * (α * (1 - θ) + θ) -
        b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ)))) ^ 2 := by
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hm : 0 < (α * (1 - θ) + θ) + θ := by positivity
  have e1 : b * (a * α * (α * (1 - θ) + θ) * (1 - θ) / (b * ((α * (1 - θ) + θ) + θ))) =
      a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ) := by
    field_simp
  rw [e1]
  rw [← sub_pos]
  have key : α ^ 2 * (a * (α * (1 - θ) + θ) -
        a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ)) ^ 2 -
      (α ^ 2 * (1 - θ) + θ) *
        (a * α - a * α * (α * (1 - θ) + θ) * (1 - θ) / ((α * (1 - θ) + θ) + θ)) ^ 2 =
      a ^ 2 * α ^ 2 * θ ^ 2 * (1 - α) * (1 - θ) *
        (α^3*(1-θ)^2 - α^2*θ^2 - 2*α^2*θ + 3*α^2 - α*θ^2 + 5*α*θ + θ^2 - θ) /
        ((α * (1 - θ) + θ) + θ) ^ 2 := by
    field_simp
    ring
  rw [key]
  positivity

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

lemma wAdm_DR (P : Params) (c w : ℝ) : wAdm P c .DR w ↔ c / μ P < w ∧ w < P.a / P.b := by
  simp [wAdm, Scenario.byDelivery]

lemma sp_eq_DR (P : Params) (c w Q q : ℝ) :
    supplierProfit P c .DR w Q q =
      P.θ * (w * min Q q) + (1 - P.θ) * (w * min (P.α * Q) q) - c * Q := by
  simp [supplierProfit, E, transfer, Scenario.byDelivery]

/-- the production policy forced by subgame perfection under pay-by-delivery -/
noncomputable def Qpol (P : Params) (c w q : ℝ) : ℝ :=
  if P.α * (1 - P.θ) * w ≤ c then q else q / P.α

/-- the retailer's order policy in DR -/
noncomputable def qpol (P : Params) (c w : ℝ) : ℝ :=
  if P.α * (1 - P.θ) * w ≤ c then qs P (μ P * w) else (P.a - P.b * w) / 2

/-- the supplier's value of posting `w` in DR -/
noncomputable def Sf (P : Params) (c w : ℝ) : ℝ :=
  if P.α * (1 - P.θ) * w ≤ c then Vf P c (μ P * w) else (w - c / P.α) * ((P.a - P.b * w) / 2)

lemma Qpol_opt (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (w q : ℝ)
    (hw : wAdm P c .DR w) (hq : 0 ≤ q) :
    0 ≤ Qpol P c w q ∧
    (∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤ supplierProfit P c .DR w (Qpol P c w q) q) ∧
    ((∀ Q' : ℝ, 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤ supplierProfit P c .DR w q q) →
      Qpol P c w q = q) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, -⟩ := (wAdm_DR P c w).mp hw
  have hwμ : c < w * (P.α * (1 - P.θ) + P.θ) := by
    rw [← hμ]; rwa [div_lt_iff₀ hμ0] at hw1
  unfold Qpol
  split_ifs with hlow
  · refine ⟨hq, fun Q' hQ' => ?_, fun _ => rfl⟩
    rw [sp_eq_DR, sp_eq_DR]
    exact YP3DA.prod_low P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ'
  · push Not at hlow
    refine ⟨by positivity, fun Q' hQ' => ?_, fun hopt => ?_⟩
    · rw [sp_eq_DR, sp_eq_DR]
      exact (YP3DA.prod_high P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ').1
    · have h1 := hopt (q / P.α) (by positivity)
      rw [sp_eq_DR, sp_eq_DR] at h1
      obtain ⟨h2, h3⟩ := YP3DA.prod_high P.α P.θ c w q q hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hq
      exact (h3 (le_antisymm h2 h1)).symm

/-- In any SPE of DR the production response is `Qpol`. -/
lemma Qchar (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (w q : ℝ) (hw : wAdm P c .DR w) (hq : 0 ≤ q) :
    σ.Q w q = Qpol P c w q := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, -⟩ := (wAdm_DR P c w).mp hw
  have hwμ : c < w * (P.α * (1 - P.θ) + P.θ) := by
    rw [← hμ]; rwa [div_lt_iff₀ hμ0] at hw1
  obtain ⟨hQ0, hQopt, htie⟩ := (hσ.1 w q hw hq).1 rfl
  unfold Qpol
  split_ifs with hlow
  · apply htie
    intro Q' hQ'
    rw [sp_eq_DR, sp_eq_DR]
    exact YP3DA.prod_low P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ'
  · push Not at hlow
    have h1 := hQopt (q / P.α) (by positivity)
    rw [sp_eq_DR, sp_eq_DR] at h1
    obtain ⟨h2, h3⟩ := YP3DA.prod_high P.α P.θ c w q (σ.Q w q) hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ0
    exact h3 (le_antisymm h2 h1)

lemma rp_noinfl (P : Params) (hP : P.Valid) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w q' p' : ℝ) (hQ : σ.Q w q' = q') (hq : 0 ≤ q') :
    retailerProfit P .DR σ w q' p' = Pi P (μ P * w) q' := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  unfold retailerProfit Pi E
  simp only [delivered, hQ, Scenario.responsive, Scenario.byDelivery, transfer, if_true]
  have h1 : min (1 * q') q' = q' := by simp
  have h2 : min (P.α * q') q' = P.α * q' := min_eq_left (by nlinarith)
  rw [h1, h2]
  have r1 := rev_opt P hP q' hq _ (hpr w q' q' hq).1 (hpr w q' q' hq).2
  have hαq : 0 ≤ P.α * q' := by positivity
  have r2 := rev_opt P hP (P.α * q') hαq _ (hpr w q' (P.α * q') hαq).1 (hpr w q' (P.α * q') hαq).2
  rw [r1, r2]
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  rw [hμ]; ring

lemma rp_infl (P : Params) (hP : P.Valid) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w q' p' : ℝ) (hQ : σ.Q w q' = q' / P.α) (hq : 0 ≤ q') :
    retailerProfit P .DR σ w q' p' = Rv P q' - w * q' := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  unfold retailerProfit E
  simp only [delivered, hQ, Scenario.responsive, Scenario.byDelivery, transfer, if_true]
  have hqα : q' ≤ q' / P.α := by rw [le_div_iff₀ hα0]; nlinarith
  have h1 : min (1 * (q' / P.α)) q' = q' := by rw [one_mul]; exact min_eq_right hqα
  have h2 : min (P.α * (q' / P.α)) q' = q' := by
    rw [mul_div_cancel₀ _ hα0.ne', min_self]
  rw [h1, h2]
  have r1 := rev_opt P hP q' hq _ (hpr w q' q' hq).1 (hpr w q' q' hq).2
  rw [r1]; ring

/-- the inflated-regime retailer problem: unique optimum `(a - b w)/2` -/
lemma infl_br (P : Params) (hP : P.Valid) (w : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a)
    (q : ℝ) (hq : 0 ≤ q) :
    Rv P q - w * q ≤ (P.a - P.b * w) ^ 2 / (4 * P.b) ∧
    (q ≠ (P.a - P.b * w) / 2 → Rv P q - w * q < (P.a - P.b * w) ^ 2 / (4 * P.b)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  rcases le_or_gt q (P.a / 2) with h | h
  · rw [Rv_le P q h]
    have e : (P.a - P.b * w) ^ 2 / (4 * P.b) - (q * (P.a - q) / P.b - w * q) =
        (q - (P.a - P.b * w) / 2) ^ 2 / P.b := by field_simp; ring
    constructor
    · have : 0 ≤ (q - (P.a - P.b * w) / 2) ^ 2 / P.b := by positivity
      linarith
    · intro hne
      have : 0 < (q - (P.a - P.b * w) / 2) ^ 2 / P.b := by
        have : q - (P.a - P.b * w) / 2 ≠ 0 := sub_ne_zero.mpr hne
        positivity
      linarith
  · rw [Rv_gt P q h]
    have e : (P.a - P.b * w) ^ 2 / (4 * P.b) - (P.a ^ 2 / (4 * P.b) - w * q) =
        (P.b * w ^ 2 / 4 + w * (q - P.a / 2)) := by field_simp; ring
    have : 0 < P.b * w ^ 2 / 4 + w * (q - P.a / 2) := by
      have : 0 < w * (q - P.a / 2) := mul_pos hw0 (by linarith)
      positivity
    exact ⟨by linarith, fun _ => by linarith⟩

lemma infl_val (P : Params) (hP : P.Valid) (w : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a) :
    Rv P ((P.a - P.b * w) / 2) - w * ((P.a - P.b * w) / 2) = (P.a - P.b * w) ^ 2 / (4 * P.b) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hw : (P.a - P.b * w) / 2 ≤ P.a / 2 := by
    have : 0 < P.b * w := mul_pos hb hw0
    linarith
  rw [Rv_le P _ hw]
  field_simp; ring

/-- consequences of subgame perfection in DR -/
lemma spe_resp (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (w : ℝ) (hw : wAdm P c .DR w) :
    σ.q w = qpol P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, hw2⟩ := (wAdm_DR P c w).mp hw
  have hw0 : 0 < w := lt_trans (div_pos hc hμ0) hw1
  have hwa : P.b * w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hw2
  have hpr := hσ.2.1 rfl
  obtain ⟨hq0, -, hopt⟩ := hσ.2.2.1 w hw
  have hQ : ∀ q, 0 ≤ q → σ.Q w q = Qpol P c w q := fun q hq => Qchar P hP c hc σ hσ w q hw hq
  unfold qpol
  split_ifs with hlow
  · have hμw : 0 < μ P * w := mul_pos hμ0 hw0
    obtain ⟨hqs0, hlt⟩ := br P hP (μ P * w) hμw
    have hQ' : ∀ q, 0 ≤ q → σ.Q w q = q := fun q hq => by rw [hQ q hq]; unfold Qpol; rw [if_pos hlow]
    by_contra hne
    have e1 := hopt (qs P (μ P * w)) (σ.p w) hqs0 (fun h => absurd h (by decide))
    rw [rp_noinfl P hP σ hpr w _ _ (hQ' _ hqs0) hqs0,
      rp_noinfl P hP σ hpr w _ _ (hQ' _ hq0) hq0] at e1
    have := hlt (σ.q w) hq0 hne
    linarith
  · have hQ' : ∀ q, 0 ≤ q → σ.Q w q = q / P.α := fun q hq => by
      rw [hQ q hq]; unfold Qpol; rw [if_neg hlow]
    have hq3 : 0 ≤ (P.a - P.b * w) / 2 := by linarith
    by_contra hne
    have e1 := hopt ((P.a - P.b * w) / 2) (σ.p w) hq3 (fun h => absurd h (by decide))
    rw [rp_infl P hP σ hpr w _ _ (hQ' _ hq3) hq3,
      rp_infl P hP σ hpr w _ _ (hQ' _ hq0) hq0, infl_val P hP w hw0 hwa] at e1
    have := (infl_br P hP w hw0 hwa (σ.q w) hq0).2 hne
    linarith

lemma qpol_nonneg (P : Params) (hP : P.Valid) (c w : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a) :
    0 ≤ qpol P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ0 : 0 < μ P := by
    have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  unfold qpol
  split_ifs
  · exact (br P hP (μ P * w) (mul_pos hμ0 hw0)).1
  · linarith

/-- supplier value of a profile following the DR policies at `w` -/
lemma SV_eq (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile) (w : ℝ)
    (hQ : σ.Q w (σ.q w) = Qpol P c w (σ.q w)) (hq : σ.q w = qpol P c w) (hq0 : 0 ≤ σ.q w) :
    supplierValue P c .DR σ w = Sf P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  unfold supplierValue Sf
  rw [sp_eq_DR, hQ]
  unfold Qpol
  split_ifs with hlow
  · rw [hq]; unfold qpol; rw [if_pos hlow]
    rw [hq] at hq0; unfold qpol at hq0; rw [if_pos hlow] at hq0
    have hαq : P.α * qs P (μ P * w) ≤ qs P (μ P * w) := by nlinarith
    rw [min_self, min_eq_left hαq]
    unfold Vf; rw [hμ]; ring
  · rw [hq]; unfold qpol; rw [if_neg hlow]
    rw [hq] at hq0; unfold qpol at hq0; rw [if_neg hlow] at hq0
    set q := (P.a - P.b * w) / 2
    have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
    have hαqα : P.α * (q / P.α) = q := by field_simp
    rw [min_eq_right hqα, hαqα, min_self]
    field_simp; ring

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

lemma qd_lt (A B c x y D : ℝ) (hD : 0 < D) (hxy : x < y) (h : B * (x + y) < A + B * c) :
    (x - c) * (A - B * x) / D < (y - c) * (A - B * y) / D := by
  rw [div_lt_div_iff_of_pos_right hD]
  nlinarith [mul_pos (sub_pos.2 hxy) (sub_pos.2 h)]

lemma qd_le (A B c x y D : ℝ) (hD : 0 < D) (hxy : x ≤ y) (h : B * (x + y) ≤ A + B * c) :
    (x - c) * (A - B * x) / D ≤ (y - c) * (A - B * y) / D := by
  rw [div_le_div_iff_of_pos_right hD]
  nlinarith [mul_nonneg (sub_nonneg.2 hxy) (sub_nonneg.2 h)]

/-- For `α ≥ 1/2`, the no-inflation supplier value `Vf` is strictly increasing up to the
center `(aμ + bc)/(2b)` of its second piece. -/
lemma Vf_mono (P : Params) (hP : P.Valid) (hα : 1 / 2 ≤ P.α) (c x y : ℝ) (hc : 0 < c)
    (hcμ : P.b * c < P.a * μ P) (hx : c < x) (hxy : x < y) (hy : 2 * (P.b * y) ≤ P.a * μ P + P.b * c) :
    Vf P c x < Vf P c y := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  have hD2 : (0:ℝ) < 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
  have hD3 : (0:ℝ) < 2 * (P.α ^ 2 * (1 - P.θ)) := by positivity
  have hgap : μ P - (P.α ^ 2 * (1 - P.θ) + P.θ) = P.α * (1 - P.θ) * (1 - P.α) := by rw [hμ]; ring
  have hgap2 : 2 * (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) ≤ P.a * (P.α * (1 - P.θ)) := by
    rw [hgap]
    have : 0 ≤ P.a * (P.α * (1 - P.θ)) * (2 * P.α - 1) := by
      apply mul_nonneg (by positivity); linarith
    nlinarith
  have hby : P.b * y < P.a * μ P := by linarith
  have hbxy : P.b * x < P.b * y := mul_lt_mul_of_pos_left hxy hb
  rcases le_or_gt (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) (P.b * x) with hx2 | hx3
  · rw [Vf_reg2 P c x (by linarith) hx2, Vf_reg2 P c y hby (by linarith)]
    apply qd_lt _ _ _ _ _ _ hD2 hxy
    linarith
  · rcases lt_or_ge (P.b * y) (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) with hy3 | hy2
    · rw [Vf_reg3 P c x hx3 hP, Vf_reg3 P c y hy3 hP]
      apply qd_lt _ _ _ _ _ _ hD3 hxy
      have : 0 < P.b * c := mul_pos hb hc
      linarith
    · rw [Vf_reg3 P c x hx3 hP, Vf_reg2 P c y hby hy2]
      set z := P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) / P.b with hz
      have hbz : P.b * z = P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
        rw [hz]; field_simp
      have hxz : x < z := by
        by_contra hh; push Not at hh
        have := mul_le_mul_of_nonneg_left hh hb.le
        linarith
      have hzy : z ≤ y := by
        by_contra hh; push Not at hh
        have := mul_lt_mul_of_pos_left hh hb
        linarith
      have e1 := qd_lt (P.a * (P.α * (1 - P.θ))) P.b c x z _ hD3 hxz (by
        have : 0 < P.b * c := mul_pos hb hc
        linarith)
      have e2 := qd_le (P.a * μ P) P.b c z y _ hD2 hzy (by linarith)
      have e3 : (z - c) * (P.a * (P.α * (1 - P.θ)) - P.b * z) / (2 * (P.α ^ 2 * (1 - P.θ))) =
          (z - c) * (P.a * μ P - P.b * z) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
        rw [hbz, hμ]
        field_simp
        ring
      linarith

/-- region-3 values lie strictly below `G3 = (bc - aα)²/(8bα²)` when `bc < a α (1-θ)` -/
lemma Vf_R3_lt (P : Params) (hP : P.Valid) (c z : ℝ) (hc : 0 < c)
    (hbc : P.b * c < P.a * (P.α * (1 - P.θ)))
    (hz3 : P.b * z < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) :
    Vf P c z < (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  rw [Vf_reg3 P c z hz3 hP]
  set u := P.α * (1 - P.θ) with hu
  have hu0 : 0 < u := by positivity
  have huα : u < P.α := by rw [hu]; nlinarith
  have hk : P.α ^ 2 * (1 - P.θ) = P.α * u := by rw [hu]; ring
  rw [hk]
  -- (z-c)(au - bz) ≤ (au - bc)²/(4b)
  have h1 : (z - c) * (P.a * u - P.b * z) ≤ (P.a * u - P.b * c) ^ 2 / (4 * P.b) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (P.a * u + P.b * c - 2 * P.b * z)]
  have h2 : P.α * (P.a * u - P.b * c) ^ 2 < u * (P.b * c - P.a * P.α) ^ 2 := by
    have hbc0 : 0 < P.b * c := mul_pos hb hc
    have e : u * (P.b * c - P.a * P.α) ^ 2 - P.α * (P.a * u - P.b * c) ^ 2 =
        (P.α - u) * (P.a ^ 2 * P.α * u - (P.b * c) ^ 2) := by ring
    have : (P.b * c) ^ 2 < P.a ^ 2 * P.α * u := by
      have : (P.b * c) ^ 2 < (P.a * u) ^ 2 := by
        apply pow_lt_pow_left₀ hbc hbc0.le (by norm_num)
      nlinarith [mul_pos (mul_pos ha ha) hu0]
    nlinarith [mul_pos (sub_pos.2 huα) (sub_pos.2 this)]
  calc (z - c) * (P.a * u - P.b * z) / (2 * (P.α * u))
      ≤ (P.a * u - P.b * c) ^ 2 / (4 * P.b) / (2 * (P.α * u)) := by
        apply div_le_div_of_nonneg_right h1 (by positivity)
    _ < (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) := by
        rw [div_div, div_lt_div_iff₀ (by positivity) (by positivity)]
        have : 0 < 8 * P.b * P.α := by positivity
        nlinarith [mul_lt_mul_of_pos_left h2 this]

/-- in region 3, the region-2 formula lies below the true value -/
lemma F2_le_Vf_R3 (P : Params) (hP : P.Valid) (c z : ℝ) (hz : c ≤ z)
    (hz3 : P.b * z < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) :
    (z - c) * (P.a * μ P - P.b * z) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ Vf P c z := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  rw [Vf_reg3 P c z hz3 hP]
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have e : (z - c) * (P.a * (P.α * (1 - P.θ)) - P.b * z) * (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) -
      (z - c) * (P.a * μ P - P.b * z) * (2 * (P.α ^ 2 * (1 - P.θ))) =
      2 * (z - c) * P.θ * (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) - P.b * z) := by
    rw [hμ]; ring
  have : 0 ≤ 2 * (z - c) * P.θ * (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) - P.b * z) := by
    apply mul_nonneg (mul_nonneg (by linarith) hθ0.le); linarith
  linarith

/-- at the switching price `w₀`, the inflated value does not exceed the non-inflated one -/
lemma g3_le_Vf (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (w0 : ℝ)
    (hw0 : P.α * (1 - P.θ) * w0 = c) (hwa : P.b * w0 < P.a) :
    (w0 - c / P.α) * ((P.a - P.b * w0) / 2) ≤ Vf P c (μ P * w0) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hw00 : 0 < w0 := by
    by_contra h; push Not at h
    have : P.α * (1 - P.θ) * w0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    linarith
  have hx : μ P * w0 - c = w0 - c / P.α := by
    rw [← hw0, hμ]; field_simp; ring
  have hxpos : 0 ≤ μ P * w0 - c := by rw [hμ, ← hw0]; nlinarith
  have hxa : P.b * (μ P * w0) < P.a * μ P := by
    have : 0 < μ P := by rw [hμ]; positivity
    nlinarith
  unfold Vf
  rw [hx]; rw [hx] at hxpos
  apply mul_le_mul_of_nonneg_left _ hxpos
  rcases le_or_gt (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ))) (P.b * (μ P * w0)) with h2 | h3
  · rw [qs_reg2 P _ hxa h2]
    rw [le_div_iff₀ (by positivity)]
    have hμs : P.α ^ 2 * (1 - P.θ) + P.θ ≤ μ P := by rw [hμ]; nlinarith
    have : 0 < P.a - P.b * w0 := by linarith
    nlinarith
  · rw [qs_reg3 P _ hxa h3]
    rw [le_div_iff₀ (by positivity)]
    rw [hμ] at h3 ⊢
    have e : P.a * (P.α * (1 - P.θ)) - P.b * ((P.α * (1 - P.θ) + P.θ) * w0) -
        (P.a - P.b * w0) / 2 * (2 * (P.α ^ 2 * (1 - P.θ))) =
        (P.a * (P.α * (1 - P.θ) + P.θ - (P.α ^ 2 * (1 - P.θ) + P.θ)) -
          P.b * ((P.α * (1 - P.θ) + P.θ) * w0)) + P.b * w0 * (P.α * (P.α * (1 - P.θ))) := by ring
    have : 0 < P.b * w0 * (P.α * (P.α * (1 - P.θ))) := by positivity
    linarith

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

/-- the comparison of the inflated optimum `G3` with the boundary value `G0` at `w₀`,
governed by `c^DR_1` -/
lemma cdr1_mul (a b α θ μ S D c1 : ℝ) (hb : 0 < b) (hD : 0 < D)
    (h : c1 = a * α * (1 - θ) * (μ ^ 2 + θ - 2 * θ * S) / (b * D)) :
    D * b * c1 = a * α * (1 - θ) * (μ ^ 2 + θ) - 2 * a * α * (1 - θ) * θ * S := by
  rw [h]; field_simp

lemma sqh1 (T M : ℝ) (hM : 0 ≤ M) (h : T ≤ -M) : 0 ≤ T ^ 2 - M ^ 2 := by nlinarith
lemma sqh2 (T M : ℝ) (hM : 0 ≤ M) (h : T < -M) : 0 < T ^ 2 - M ^ 2 := by nlinarith
lemma sqh3 (T M : ℝ) (h1 : -M < T) (h2 : T < M) : T ^ 2 - M ^ 2 < 0 := by nlinarith
lemma sqh4 (T M : ℝ) (hM : 0 ≤ M) (h : T ^ 2 - M ^ 2 < 0) : T < M := by nlinarith

lemma thrAB (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) :
    (c ≤ cDR1 P → μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤
        (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (c < cDR1 P → μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) <
        (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (cDR1 P < c → c < cDR2 P → (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
        μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  set S := Real.sqrt (P.α * μ P * (1 - P.α) * (1 - P.θ)) with hSdef
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hS : S ^ 2 = P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.α) * (1 - P.θ) := by
    rw [hSdef, Real.sq_sqrt (by positivity), hμ]
  set d := P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) + P.θ * (1 + P.θ) ^ 2 with hd
  have hd0 : 0 < d := by positivity
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  set M := 2 * P.a * P.α * (1 - P.θ) * P.θ * S with hM
  have hM0 : 0 ≤ M := by positivity
  have key : ∀ c : ℝ, (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) -
      μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) =
      ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 - M ^ 2) /
      (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
    intro c
    rw [hμ]
    exact G3_sub_G0 P.a P.b P.α P.θ c S hb hα0 hθ0 hθ1 hS
  have hden : 0 < 8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d := by
    positivity
  -- `b d c^DR_1 = aα(1-θ)(μ²+θ) - M`
  have hc1 : d * P.b * cDR1 P = P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) - M := by
    have := cdr1_mul P.a P.b P.α P.θ (μ P) S d (cDR1 P) hb hd0 (by unfold cDR1; rw [← hSdef, ← hd])
    rw [this, hM, hμ]
  have hT2 := T_c2 P.a P.b P.α P.θ S ha hb hα0 hα1 hθ0 hθ1 (K_pos P.α P.θ hα hα1 hθ0 hθ1) hS
  have hc2 : cDR2 P = P.a * P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) /
      (P.b * ((P.α * (1 - P.θ) + P.θ) + P.θ)) := by
    unfold cDR2; rw [hμ]
  rw [← hd, ← hM, ← hc2] at hT2
  refine ⟨fun h => ?_, fun h => ?_, fun h1 h2 => ?_⟩
  · have hT : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) ≤ -M := by
      have := mul_le_mul_of_nonneg_left h (by positivity : (0:ℝ) ≤ d * P.b)
      linarith
    have : 0 ≤ ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
      exact div_nonneg (sqh1 _ _ hM0 hT) hden.le
    linarith [key c]
  · have hT : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < -M := by
      have := mul_lt_mul_of_pos_left h (by positivity : (0:ℝ) < d * P.b)
      linarith
    have : 0 < ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) := by
      exact div_pos (sqh2 _ _ hM0 hT) hden
    linarith [key c]
  · have hT1 : -M < d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) := by
      have := mul_lt_mul_of_pos_left h1 (by positivity : (0:ℝ) < d * P.b)
      linarith
    have hTc2 : d * P.b * cDR2 P - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < M :=
      sqh4 _ _ hM0 hT2
    have hT2' : d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ) < M := by
      have := mul_lt_mul_of_pos_left h2 (by positivity : (0:ℝ) < d * P.b)
      linarith
    have : ((d * P.b * c - P.a * P.α * (1 - P.θ) * ((P.α * (1 - P.θ) + P.θ) ^ 2 + P.θ)) ^ 2 -
        M ^ 2) / (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * d) < 0 := by
      exact div_neg_of_neg_of_pos (sqh3 _ _ hT1 hT2') hden
    linarith [key c]

/-- above `c^DR_2` (and below `aα/b`), the inflated optimum is below the no-inflation optimum -/
lemma thrC (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc2 : cDR2 P ≤ c)
    (hca : P.b * c < P.a * P.α) :
    (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) <
      (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  set s := Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ) with hsdef
  have hs0 : 0 < s := Real.sqrt_pos.mpr hs2
  have hs : s ^ 2 = P.α ^ 2 * (1 - P.θ) + P.θ := Real.sq_sqrt hs2.le
  have hsα : P.α < s := by
    rw [hsdef]; apply Real.lt_sqrt_of_sq_lt
    nlinarith [mul_pos hθ0 (by nlinarith : (0:ℝ) < 1 - P.α ^ 2)]
  have hαμ : P.α < μ P := by rw [hμ]; nlinarith
  have hc2' : cDR2 P = P.a * P.α * (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) /
      (P.b * ((P.α * (1 - P.θ) + P.θ) + P.θ)) := by
    unfold cDR2; rw [hμ]
  have hC := caseC_c2 P.a P.b P.α P.θ ha hb hα0 hα1 hθ0 hθ1 (K_pos P.α P.θ hα hα1 hθ0 hθ1)
  rw [← hc2', ← hμ] at hC
  -- positivity of the two sides at c₂
  have hc2a : P.b * cDR2 P < P.a * P.α := by
    rw [hc2']
    have hm : 0 < (P.α * (1 - P.θ) + P.θ) + P.θ := by positivity
    rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
    have : (P.α * (1 - P.θ) + P.θ) * (1 - P.θ) < (P.α * (1 - P.θ) + P.θ) + P.θ := by nlinarith
    nlinarith [mul_lt_mul_of_pos_left this (mul_pos hb (mul_pos ha hα0))]
  have hA : 0 ≤ s * (P.a * P.α - P.b * cDR2 P) := by
    apply mul_nonneg hs0.le; linarith
  have hB : 0 ≤ P.α * (P.a * μ P - P.b * cDR2 P) := by
    apply mul_nonneg hα0.le; nlinarith [mul_pos ha hα0]
  have hf2 : s * (P.a * P.α - P.b * cDR2 P) < P.α * (P.a * μ P - P.b * cDR2 P) := by
    have h1 : (s * (P.a * P.α - P.b * cDR2 P)) ^ 2 < (P.α * (P.a * μ P - P.b * cDR2 P)) ^ 2 := by
      rw [mul_pow, mul_pow, hs]; linarith
    exact lt_of_pow_lt_pow_left₀ 2 hB h1
  have hf : s * (P.a * P.α - P.b * c) < P.α * (P.a * μ P - P.b * c) := by
    have : (P.b * c - P.b * cDR2 P) * (s - P.α) ≥ 0 :=
      mul_nonneg (by nlinarith) (by linarith)
    nlinarith
  have hA' : 0 ≤ s * (P.a * P.α - P.b * c) := by apply mul_nonneg hs0.le; linarith
  have hsq : (s * (P.a * P.α - P.b * c)) ^ 2 < (P.α * (P.a * μ P - P.b * c)) ^ 2 :=
    pow_lt_pow_left₀ hf hA' (by norm_num)
  rw [mul_pow, mul_pow, hs] at hsq
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have e : (P.b * c - P.a * P.α) ^ 2 = (P.a * P.α - P.b * c) ^ 2 := by ring
  rw [e]
  nlinarith [mul_lt_mul_of_pos_left hsq (by positivity : (0:ℝ) < 8 * P.b)]

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

lemma Sf_infl (P : Params) (hP : P.Valid) (c w : ℝ) (h : c < P.α * (1 - P.θ) * w) :
    Sf P c w = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) -
      P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  unfold Sf; rw [if_neg (not_le.mpr h)]
  field_simp; ring

lemma Sf_noinfl (P : Params) (c w : ℝ) (h : P.α * (1 - P.θ) * w ≤ c) :
    Sf P c w = Vf P c (μ P * w) := by
  unfold Sf; rw [if_pos h]

/-- basic threshold facts used in all three cases -/
lemma basics (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    cOR P < 0 ∧ cDR1 P < cDR2 P ∧ 0 < cDR2 P ∧
    P.b * cDR2 P * (1 + P.θ) ≤ P.a * (P.α * (1 - P.θ)) ∧
    P.b * cDR2 P * (μ P + P.θ) = P.a * (P.α * (1 - P.θ)) * μ P := by
  obtain ⟨h1, h2, -⟩ := threshold_order P hP hα
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hμ1 : μ P ≤ 1 := by rw [hμ]; nlinarith
  have e : P.b * cDR2 P * (μ P + P.θ) = P.a * (P.α * (1 - P.θ)) * μ P := by
    unfold cDR2; field_simp
  have hc2p : 0 < cDR2 P := by
    unfold cDR2
    exact div_pos (mul_pos (mul_pos (mul_pos ha hα0) hμ0) h1θ) (mul_pos hb (by linarith))
  refine ⟨h1, h2, ?_, ?_, e⟩
  · exact hc2p
  · have hpos : 0 < P.b * cDR2 P := mul_pos hb hc2p
    have : P.b * cDR2 P * (1 + P.θ) * μ P ≤ P.b * cDR2 P * (μ P + P.θ) := by
      nlinarith [mul_pos hpos hθ0]
    rw [e] at this
    exact le_of_mul_le_mul_right this hμ0

/-- for `c ≤ c^DR_2`, the non-inflated values are maximized at `w₀ = c/(α(1-θ))` -/
lemma noinfl_mono (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc : 0 < c)
    (hcμ : P.b * c < P.a * μ P) (hc2 : c ≤ cDR2 P) (w : ℝ) (hw : wAdm P c .DR w)
    (hlow : P.α * (1 - P.θ) * w ≤ c) :
    Vf P c (μ P * w) ≤ Vf P c (μ P * (c / (P.α * (1 - P.θ)))) ∧
    (P.α * (1 - P.θ) * w < c → Vf P c (μ P * w) < Vf P c (μ P * (c / (P.α * (1 - P.θ))))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  obtain ⟨-, -, -, -, e2⟩ := basics P hP hα
  obtain ⟨hw1, -⟩ := (wAdm_DR P c w).mp hw
  have hx : c < μ P * w := by rw [div_lt_iff₀ hμ0] at hw1; linarith
  have hy : 2 * (P.b * (μ P * (c / (P.α * (1 - P.θ))))) ≤ P.a * μ P + P.b * c := by
    have h3 : P.b * c * (μ P + P.θ) ≤ P.a * (P.α * (1 - P.θ)) * μ P := by
      rw [← e2]; apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hc2 hb.le
    rw [show 2 * (P.b * (μ P * (c / (P.α * (1 - P.θ))))) =
      2 * P.b * μ P * c / (P.α * (1 - P.θ)) by ring, div_le_iff₀ hu0]
    have : 2 * μ P - P.α * (1 - P.θ) = μ P + P.θ := by rw [hμ]; ring
    have h4 : P.b * c * (2 * μ P - P.α * (1 - P.θ)) ≤ P.a * (P.α * (1 - P.θ)) * μ P := by
      rw [this]; exact h3
    nlinarith [h4]
  have hmono : P.α * (1 - P.θ) * w < c →
      Vf P c (μ P * w) < Vf P c (μ P * (c / (P.α * (1 - P.θ)))) := by
    intro hlt
    apply Vf_mono P hP (by linarith) c _ _ hc hcμ hx _ hy
    apply mul_lt_mul_of_pos_left _ hμ0
    rw [lt_div_iff₀ hu0]; linarith
  refine ⟨?_, hmono⟩
  rcases hlow.lt_or_eq with h | h
  · exact (hmono h).le
  · have : w = c / (P.α * (1 - P.θ)) := by field_simp; linarith
    rw [this]

/-- the value at `w₀`: the region-2 formula `G0`, or (in region 3) below `G3` -/
lemma val_w0 (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c)
    (hbc : P.b * c < P.a * (P.α * (1 - P.θ))) :
    (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (μ P * (c / (P.α * (1 - P.θ)))) →
      Vf P c (μ P * (c / (P.α * (1 - P.θ)))) = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
    (P.b * (μ P * (c / (P.α * (1 - P.θ)))) < P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) →
      Vf P c (μ P * (c / (P.α * (1 - P.θ)))) < (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤
        Vf P c (μ P * (c / (P.α * (1 - P.θ))))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  have hxa : P.b * (μ P * (c / (P.α * (1 - P.θ)))) < P.a * μ P := by
    have h5 : P.b * c / (P.α * (1 - P.θ)) < P.a := by rw [div_lt_iff₀ hu0]; linarith
    calc P.b * (μ P * (c / (P.α * (1 - P.θ)))) = μ P * (P.b * c / (P.α * (1 - P.θ))) := by ring
      _ < μ P * P.a := mul_lt_mul_of_pos_left h5 hμ0
      _ = P.a * μ P := by ring
  have hform : (μ P * (c / (P.α * (1 - P.θ))) - c) * (P.a * μ P - P.b * (μ P * (c / (P.α * (1 - P.θ))))) /
      (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    rw [hμ]; field_simp; ring
  have hcx : c ≤ μ P * (c / (P.α * (1 - P.θ))) := by
    rw [mul_div_assoc', le_div_iff₀ hu0, hμ]; nlinarith
  refine ⟨fun h2 => ?_, fun h3 => ⟨Vf_R3_lt P hP c _ hc hbc h3, ?_⟩⟩
  · rw [Vf_reg2 P c _ hxa h2, hform]
  · rw [← hform]; exact F2_le_Vf_R3 P hP c _ hcx h3

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

lemma g3_form (a b α c w : ℝ) (hb : 0 < b) (hα0 : 0 < α) :
    (w - c / α) * ((a - b * w) / 2) =
      (b * c - a * α) ^ 2 / (8 * b * α ^ 2) - b / 2 * (w - (a / b + c / α) / 2) ^ 2 := by
  field_simp; ring

/-- Case A: `c ≤ c^DR_1`; the supplier optimum is the inflated price `w₃`. -/
lemma caseA (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc : 0 < c)
    (hcμ : P.b * c < P.a * μ P) (hc1 : c ≤ cDR1 P) :
    wAdm P c .DR ((P.a / P.b + c / P.α) / 2) ∧
    c < P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) ∧
    Sf P c ((P.a / P.b + c / P.α) / 2) = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
    (∀ w, wAdm P c .DR w → Sf P c w ≤ (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) ∧
    (c < cDR1 P → ∀ w, wAdm P c .DR w →
      Sf P c w = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) → w = (P.a / P.b + c / P.α) / 2) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  have huμ : P.α * (1 - P.θ) < μ P := by rw [hμ]; linarith
  have huα : P.α * (1 - P.θ) < P.α := by nlinarith
  obtain ⟨-, h12, -, h2u, -⟩ := basics P hP hα
  have hc2 : c < cDR2 P := lt_of_le_of_lt hc1 h12
  have hbc1 : P.b * c * (1 + P.θ) < P.a * (P.α * (1 - P.θ)) := by
    have := mul_lt_mul_of_pos_left hc2 hb
    nlinarith
  have hbc : P.b * c < P.a * (P.α * (1 - P.θ)) := by nlinarith [mul_pos (mul_pos hb hc) hθ0]
  set w3 := (P.a / P.b + c / P.α) / 2 with hw3
  have hinfl : c < P.α * (1 - P.θ) * w3 := by
    have e : P.α * (1 - P.θ) * w3 - c = (P.a * (P.α * (1 - P.θ)) - P.b * c * (1 + P.θ)) / (2 * P.b) := by
      rw [hw3]; field_simp; ring
    have : 0 < (P.a * (P.α * (1 - P.θ)) - P.b * c * (1 + P.θ)) / (2 * P.b) := by
      apply div_pos _ (by positivity); linarith
    linarith
  have hadm : wAdm P c .DR w3 := by
    rw [wAdm_DR]
    constructor
    · have h1 : c / μ P < c / (P.α * (1 - P.θ)) := div_lt_div_of_pos_left hc hu0 huμ
      have h2 : c / (P.α * (1 - P.θ)) < w3 := by rw [div_lt_iff₀ hu0]; linarith
      linarith
    · rw [hw3]
      have : c / P.α < P.a / P.b := by
        rw [div_lt_div_iff₀ hα0 hb]; nlinarith
      linarith
  have hval : Sf P c w3 = (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) := by
    rw [Sf_infl P hP c w3 hinfl, hw3]; ring
  obtain ⟨hAB1, hAB2, -⟩ := thrAB P hP hα c
  have hno : ∀ w, wAdm P c .DR w → P.α * (1 - P.θ) * w ≤ c →
      Sf P c w ≤ (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) ∧
      (c < cDR1 P → Sf P c w < (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2)) := by
    intro w hw hlow
    rw [Sf_noinfl P c w hlow]
    have hm := (noinfl_mono P hP hα c hc hcμ hc2.le w hw hlow).1
    obtain ⟨v2, v3⟩ := val_w0 P hP c hc hbc
    rcases le_or_gt (P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)))
        (P.b * (μ P * (c / (P.α * (1 - P.θ))))) with hr | hr
    · rw [v2 hr] at hm
      exact ⟨le_trans hm (hAB1 hc1), fun h => lt_of_le_of_lt hm (hAB2 h)⟩
    · have := (v3 hr).1
      exact ⟨by linarith, fun _ => by linarith⟩
  refine ⟨hadm, hinfl, hval, fun w hw => ?_, fun hlt w hw heq => ?_⟩
  · by_cases hlow : P.α * (1 - P.θ) * w ≤ c
    · exact (hno w hw hlow).1
    · push Not at hlow
      rw [Sf_infl P hP c w hlow]
      have : 0 ≤ P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by positivity
      linarith
  · by_cases hlow : P.α * (1 - P.θ) * w ≤ c
    · have := (hno w hw hlow).2 hlt
      linarith
    · push Not at hlow
      rw [Sf_infl P hP c w hlow] at heq
      have h0 : P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 = 0 := by linarith
      have : (w - (P.a / P.b + c / P.α) / 2) ^ 2 = 0 := by
        rcases mul_eq_zero.mp h0 with h | h
        · linarith
        · exact h
      have := pow_eq_zero_iff (two_ne_zero) |>.mp this
      linarith

/-- Case B: `c^DR_1 < c < c^DR_2`; the supplier optimum is the kink `w₀ = c/(α(1-θ))`. -/
lemma caseB (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc : 0 < c)
    (hcμ : P.b * c < P.a * μ P) (hc1 : cDR1 P < c) (hc2 : c < cDR2 P) :
    wAdm P c .DR (c / (P.α * (1 - P.θ))) ∧
    P.α * (1 - P.θ) * (c / (P.α * (1 - P.θ))) ≤ c ∧
    P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (μ P * (c / (P.α * (1 - P.θ)))) ∧
    Sf P c (c / (P.α * (1 - P.θ))) = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    (∀ w, wAdm P c .DR w → Sf P c w ≤ μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      (Sf P c w = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) → w = c / (P.α * (1 - P.θ)))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  have huμ : P.α * (1 - P.θ) < μ P := by rw [hμ]; linarith
  obtain ⟨-, -, -, h2u, -⟩ := basics P hP hα
  have hbc1 : P.b * c * (1 + P.θ) < P.a * (P.α * (1 - P.θ)) := by
    have := mul_lt_mul_of_pos_left hc2 hb
    nlinarith
  have hbc : P.b * c < P.a * (P.α * (1 - P.θ)) := by nlinarith [mul_pos (mul_pos hb hc) hθ0]
  set w0 := c / (P.α * (1 - P.θ)) with hw0
  have hw0e : P.α * (1 - P.θ) * w0 = c := by rw [hw0]; field_simp
  have hadm : wAdm P c .DR w0 := by
    rw [wAdm_DR]
    refine ⟨div_lt_div_of_pos_left hc hu0 huμ, ?_⟩
    rw [hw0, div_lt_div_iff₀ hu0 hb]; linarith
  obtain ⟨-, -, hAB3⟩ := thrAB P hP hα c
  have hG := hAB3 hc1 hc2
  obtain ⟨v2, v3⟩ := val_w0 P hP c hc hbc
  have hreg : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (μ P * w0) := by
    by_contra hr; push Not at hr
    obtain ⟨h1, h2⟩ := v3 hr
    linarith
  have hval : Sf P c w0 = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
        (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    rw [Sf_noinfl P c w0 hw0e.le, v2 hreg]
  refine ⟨hadm, hw0e.le, hreg, hval, fun w hw => ?_⟩
  by_cases hlow : P.α * (1 - P.θ) * w ≤ c
  · rcases hlow.lt_or_eq with hlt | heq
    · have := (noinfl_mono P hP hα c hc hcμ hc2.le w hw hlow).2 hlt
      rw [Sf_noinfl P c w hlow]
      rw [← Sf_noinfl P c w0 hw0e.le, hval] at this
      exact ⟨this.le, fun h => absurd h (ne_of_lt this)⟩
    · have : w = w0 := by rw [hw0]; field_simp; linarith
      rw [this, hval]; exact ⟨le_rfl, fun _ => rfl⟩
  · push Not at hlow
    rw [Sf_infl P hP c w hlow]
    have : 0 ≤ P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by positivity
    exact ⟨by linarith, fun h => by linarith⟩

/-- Case C: `c ≥ c^DR_2`; the supplier optimum is the interior non-inflated price `w₂`. -/
lemma caseC (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) (c : ℝ) (hc : 0 < c)
    (hcμ : P.b * c < P.a * μ P) (hc2 : cDR2 P ≤ c) :
    wAdm P c .DR ((P.a * μ P + P.b * c) / (2 * P.b * μ P)) ∧
    P.α * (1 - P.θ) * ((P.a * μ P + P.b * c) / (2 * P.b * μ P)) ≤ c ∧
    μ P * ((P.a * μ P + P.b * c) / (2 * P.b * μ P)) = (P.a * μ P + P.b * c) / (2 * P.b) ∧
    Sf P c ((P.a * μ P + P.b * c) / (2 * P.b * μ P)) =
      (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    (∀ w, wAdm P c .DR w → Sf P c w ≤ (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      (Sf P c w = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) →
        w = (P.a * μ P + P.b * c) / (2 * P.b * μ P))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hμ1 : μ P ≤ 1 := by rw [hμ]; nlinarith
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  obtain ⟨hOR, -, -, h2u, e2⟩ := basics P hP hα
  have hcOR : cOR P < c := by linarith
  set w2' := (P.a * μ P + P.b * c) / (2 * P.b) with hw2'
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := sup2 P hP c hc hcμ hcOR.le w2' (by rw [hw2'])
  set w2 := (P.a * μ P + P.b * c) / (2 * P.b * μ P) with hw2
  have hμw2 : μ P * w2 = w2' := by rw [hw2, hw2']; field_simp
  have hlow2 : P.α * (1 - P.θ) * w2 ≤ c := by
    have h3 : P.a * (P.α * (1 - P.θ)) * μ P ≤ P.b * c * (μ P + P.θ) := by
      rw [← e2]; apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hc2 hb.le
    rw [hw2, mul_div_assoc', div_le_iff₀ (by positivity)]
    have : 2 * μ P - P.α * (1 - P.θ) = μ P + P.θ := by rw [hμ]; ring
    have h4 : P.a * (P.α * (1 - P.θ)) * μ P ≤ P.b * c * (2 * μ P - P.α * (1 - P.θ)) := by
      rw [this]; exact h3
    nlinarith [h4]
  have hadm : wAdm P c .DR w2 := by
    rw [wAdm_DR]
    constructor
    · rw [div_lt_iff₀ hμ0, mul_comm, hμw2]; exact s1
    · rw [hw2, div_lt_div_iff₀ (by positivity) hb]; nlinarith
  have hval : Sf P c w2 = (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    rw [Sf_noinfl P c w2 hlow2, hμw2, s6]
  refine ⟨hadm, hlow2, hμw2, hval, fun w hw => ?_⟩
  obtain ⟨hw1, hwa⟩ := (wAdm_DR P c w).mp hw
  by_cases hlow : P.α * (1 - P.θ) * w ≤ c
  · rw [Sf_noinfl P c w hlow, ← s6]
    have hx1 : c < μ P * w := by rw [div_lt_iff₀ hμ0] at hw1; linarith
    have hx2 : μ P * w < P.a / P.b := by
      have : 0 < w := lt_trans (div_pos hc hμ0) hw1
      nlinarith
    obtain ⟨hle, hlt⟩ := s7 (μ P * w) hx1 hx2
    refine ⟨hle, fun h => ?_⟩
    by_contra hne
    have : μ P * w ≠ w2' := by
      intro h'; apply hne; rw [← hμw2] at h'; exact mul_left_cancel₀ hμ0.ne' h'
    have := hlt hcOR this
    linarith
  · push Not at hlow
    rw [Sf_infl P hP c w hlow]
    have hsq : 0 ≤ P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by positivity
    suffices hlt : (P.b * c - P.a * P.α) ^ 2 / (8 * P.b * P.α ^ 2) -
        P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 <
        (P.a * μ P - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) from
      ⟨hlt.le, fun h => absurd h (ne_of_lt hlt)⟩
    by_cases h3 : P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) ≤ c
    · -- `w₃ ≤ w₀ < w`
      set w0 := c / (P.α * (1 - P.θ)) with hw0
      have hw0e : P.α * (1 - P.θ) * w0 = c := by rw [hw0]; field_simp
      have hw0w : w0 < w := by rw [hw0, div_lt_iff₀ hu0]; linarith
      have hw30 : (P.a / P.b + c / P.α) / 2 ≤ w0 := by
        rw [hw0, le_div_iff₀ hu0]; linarith
      have hwa' : w < P.a / P.b := hwa
      have hbw0 : P.b * w0 < P.a := by
        have := (lt_div_iff₀ hb).mp (lt_trans hw0w hwa'); linarith
      have hg := g3_le_Vf P hP c hc w0 hw0e hbw0
      rw [g3_form P.a P.b P.α c w0 hb hα0] at hg
      have hx1 : c < μ P * w0 := by
        have huμ' : P.α * (1 - P.θ) < μ P := by rw [hμ]; linarith
        rw [hw0, mul_div_assoc', lt_div_iff₀ hu0]
        linarith [mul_lt_mul_of_pos_left huμ' hc]
      have hx2 : μ P * w0 < P.a / P.b := by
        have : 0 < w0 := by rw [hw0]; positivity
        calc μ P * w0 ≤ 1 * w0 := mul_le_mul_of_nonneg_right hμ1 this.le
          _ < P.a / P.b := by rw [one_mul]; exact lt_trans hw0w hwa'
      have hV := (s7 (μ P * w0) hx1 hx2).1
      rw [s6] at hV
      have hsq2 : (w0 - (P.a / P.b + c / P.α) / 2) ^ 2 < (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by
        apply pow_lt_pow_left₀ (by linarith) (by linarith) (by norm_num)
      have : P.b / 2 * (w0 - (P.a / P.b + c / P.α) / 2) ^ 2 <
          P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 :=
        mul_lt_mul_of_pos_left hsq2 (by positivity)
      linarith
    · push Not at h3
      have hbc1 : P.b * c * (1 + P.θ) < P.a * (P.α * (1 - P.θ)) := by
        have e : P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) - c =
            (P.a * (P.α * (1 - P.θ)) - P.b * c * (1 + P.θ)) / (2 * P.b) := by
          field_simp; ring
        have : 0 < (P.a * (P.α * (1 - P.θ)) - P.b * c * (1 + P.θ)) / (2 * P.b) := by linarith
        have := (div_pos_iff_of_pos_right (by positivity : (0:ℝ) < 2 * P.b)).mp this
        linarith
      have hca : P.b * c < P.a * P.α := by
        have e1 : P.b * c ≤ P.b * c * (1 + P.θ) :=
          le_mul_of_one_le_right (mul_pos hb hc).le (by linarith)
        have huα : P.α * (1 - P.θ) < P.α := by linarith [mul_pos hα0 hθ0]
        have e2 := mul_lt_mul_of_pos_left huα ha
        linarith
      have := thrC P hP hα c hc2 hca
      linarith

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

/-- the profile that follows the DR policies and posts `w` -/
noncomputable def prof (P : Params) (c w : ℝ) : Profile where
  w := w
  Q := fun w q => Qpol P c w q
  q := fun w => qpol P c w
  p := fun _ => P.a / (2 * P.b)
  pr := fun _ _ x => prf P x

/-- a profile following the policies is an SPE as soon as `w` maximizes `Sf` -/
lemma prof_spe (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (w : ℝ)
    (hw : wAdm P c .DR w) (hmax : ∀ w', wAdm P c .DR w' → Sf P c w' ≤ Sf P c w) :
    IsSPE P c .DR (prof P c w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hpr : ∀ w q x : ℝ, 0 ≤ x → pAdm P ((prof P c w).pr w q x) ∧
      ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P ((prof P c w).pr w q x) x := by
    intro w' q x hx; exact prf_opt P hP x hx
  have hpr' : ∀ w' q x : ℝ, 0 ≤ x → pAdm P ((prof P c w).pr w' q x) ∧
      ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P ((prof P c w).pr w' q x) x := by
    intro w' q x hx; exact prf_opt P hP x hx
  have hpos : ∀ w', wAdm P c .DR w' → 0 < w' ∧ P.b * w' < P.a := by
    intro w' hw'
    obtain ⟨h1, h2⟩ := (wAdm_DR P c w').mp hw'
    exact ⟨lt_trans (div_pos hc hμ0) h1, by rwa [lt_div_iff₀ hb, mul_comm] at h2⟩
  refine ⟨fun w' q hw' hq => ⟨fun _ => Qpol_opt P hP c hc w' q hw' hq, fun h => by
      simp [Scenario.byDelivery] at h⟩, fun _ => hpr', fun w' hw' => ?_, hw, fun w' hw' => ?_⟩
  · obtain ⟨hw0, hwa⟩ := hpos w' hw'
    refine ⟨qpol_nonneg P hP c w' hw0 hwa, fun h => by simp [Scenario.responsive] at h,
      fun q' p' hq' _ => ?_⟩
    show retailerProfit P .DR (prof P c w) w' q' p' ≤
      retailerProfit P .DR (prof P c w) w' (qpol P c w') (P.a / (2 * P.b))
    have hq0 := qpol_nonneg P hP c w' hw0 hwa
    by_cases hlow : P.α * (1 - P.θ) * w' ≤ c
    · have hQ : ∀ q, (prof P c w).Q w' q = q := fun q => by
        show Qpol P c w' q = q; unfold Qpol; rw [if_pos hlow]
      rw [rp_noinfl P hP _ hpr' w' q' p' (hQ q') hq', rp_noinfl P hP _ hpr' w' _ _ (hQ _) hq0]
      unfold qpol; rw [if_pos hlow]
      obtain ⟨-, hlt⟩ := br P hP (μ P * w') (mul_pos hμ0 hw0)
      by_cases he : q' = qs P (μ P * w')
      · rw [he]
      · exact (hlt q' hq' he).le
    · have hQ : ∀ q, (prof P c w).Q w' q = q / P.α := fun q => by
        show Qpol P c w' q = q / P.α; unfold Qpol; rw [if_neg hlow]
      rw [rp_infl P hP _ hpr' w' q' p' (hQ q') hq', rp_infl P hP _ hpr' w' _ _ (hQ _) hq0]
      unfold qpol; rw [if_neg hlow, infl_val P hP w' hw0 hwa]
      exact (infl_br P hP w' hw0 hwa q' hq').1
  · obtain ⟨hw0, hwa⟩ := hpos w' hw'
    obtain ⟨hw0', hwa'⟩ := hpos w hw
    have e1 := SV_eq P hP c (prof P c w) w' rfl rfl (qpol_nonneg P hP c w' hw0 hwa)
    have e2 := SV_eq P hP c (prof P c w) (prof P c w).w rfl rfl (qpol_nonneg P hP c w hw0' hwa')
    rw [e1, e2]
    exact hmax w' hw'

/-- the consequences of subgame perfection in DR -/
lemma spe_char (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) :
    wAdm P c .DR σ.w ∧ (∀ w', wAdm P c .DR w' → Sf P c w' ≤ Sf P c σ.w) ∧
    σ.q σ.w = qpol P c σ.w ∧ σ.Q σ.w (σ.q σ.w) = Qpol P c σ.w (σ.q σ.w) ∧
    supplierValue P c .DR σ σ.w = Sf P c σ.w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by
    rw [hμ]
    have : 0 < 1 - P.θ := by linarith
    positivity
  have hSV : ∀ w', wAdm P c .DR w' → supplierValue P c .DR σ w' = Sf P c w' := by
    intro w' hw'
    obtain ⟨h1, h2⟩ := (wAdm_DR P c w').mp hw'
    have hw0 : 0 < w' := lt_trans (div_pos hc hμ0) h1
    have hwa : P.b * w' < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at h2
    have hq := spe_resp P hP c hc σ hσ w' hw'
    have hq0 : 0 ≤ σ.q w' := by rw [hq]; exact qpol_nonneg P hP c w' hw0 hwa
    exact SV_eq P hP c σ w' (Qchar P hP c hc σ hσ w' _ hw' hq0) hq hq0
  obtain ⟨hwσ, hopt⟩ := hσ.2.2.2
  have hq0 : 0 ≤ σ.q σ.w := (hσ.2.2.1 σ.w hwσ).1
  refine ⟨hwσ, fun w' hw' => ?_, spe_resp P hP c hc σ hσ σ.w hwσ,
    Qchar P hP c hc σ hσ σ.w _ hwσ hq0, hSV σ.w hwσ⟩
  rw [← hSV w' hw', ← hSV σ.w hwσ]
  exact hopt w' hw'

lemma CS_eq (P : Params) (c : ℝ) (σ : Profile) :
    CS P c .DR σ =
      P.θ * surplus P (σ.pr σ.w (σ.q σ.w) (min (1 * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)))
          (min (1 * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) +
      (1 - P.θ) * surplus P (σ.pr σ.w (σ.q σ.w) (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)))
          (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) := by
  simp only [CS, E, delivered, Scenario.responsive, if_true]

/-- outcome when the equilibrium price is in the inflated regime -/
lemma outcome_infl (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w / P.α) (hq : σ.q σ.w = (P.a - P.b * σ.w) / 2)
    (hw0 : 0 < σ.w) (hwa : P.b * σ.w < P.a) :
    piR P c .DR σ = (P.a - P.b * σ.w) ^ 2 / (4 * P.b) ∧
    CS P c .DR σ = ((P.a - P.b * σ.w) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hq0 : 0 ≤ σ.q σ.w := by rw [hq]; linarith
  constructor
  · show retailerProfit P .DR σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_infl P hP σ hpr _ _ _ hQ hq0, hq]
    exact infl_val P hP _ hw0 hwa
  · rw [CS_eq, hQ]
    have hqα : σ.q σ.w ≤ σ.q σ.w / P.α := by rw [le_div_iff₀ hα0]; nlinarith
    have hαqα : P.α * (σ.q σ.w / P.α) = σ.q σ.w := by field_simp
    rw [one_mul, min_eq_right hqα, hαqα, min_self]
    have hpos : 0 < σ.q σ.w := by rw [hq]; linarith
    have hle : σ.q σ.w ≤ P.a / 2 := by rw [hq]; nlinarith
    have hs := surplus_opt P hP _ hpos _ (hpr σ.w (σ.q σ.w) _ hpos.le).1 (hpr σ.w (σ.q σ.w) _ hpos.le).2
    rw [hs]
    unfold Sv; rw [if_pos hle, hq]; ring

/-- outcome when the equilibrium price is in the non-inflated regime with order `q₀ ≤ a/2` -/
lemma outcome_noinfl (P : Params) (hP : P.Valid) (c : ℝ) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (hQ : σ.Q σ.w (σ.q σ.w) = σ.q σ.w) (hpos : 0 < σ.q σ.w) (hle : σ.q σ.w ≤ P.a / 2) :
    piR P c .DR σ = P.θ * (σ.q σ.w * (P.a - σ.q σ.w) / P.b) +
        (1 - P.θ) * (P.α * σ.q σ.w * (P.a - P.α * σ.q σ.w) / P.b) - μ P * σ.w * σ.q σ.w ∧
    CS P c .DR σ = P.θ * ((σ.q σ.w) ^ 2 / (2 * P.b)) +
        (1 - P.θ) * ((P.α * σ.q σ.w) ^ 2 / (2 * P.b)) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hαq : P.α * σ.q σ.w ≤ σ.q σ.w := by nlinarith
  have hαle : P.α * σ.q σ.w ≤ P.a / 2 := le_trans hαq hle
  have hαpos : 0 < P.α * σ.q σ.w := mul_pos hα0 hpos
  constructor
  · show retailerProfit P .DR σ σ.w (σ.q σ.w) (σ.p σ.w) = _
    rw [rp_noinfl P hP σ hpr _ _ _ hQ hpos.le]
    unfold Pi; rw [Rv_le P _ hle, Rv_le P _ hαle]
  · rw [CS_eq, hQ, one_mul, min_self, min_eq_left hαq]
    rw [surplus_opt P hP _ hpos _ (hpr σ.w (σ.q σ.w) _ hpos.le).1 (hpr σ.w (σ.q σ.w) _ hpos.le).2,
      surplus_opt P hP _ hαpos _ (hpr σ.w (σ.q σ.w) _ hαpos.le).1 (hpr σ.w (σ.q σ.w) _ hαpos.le).2]
    unfold Sv; rw [if_pos hle, if_pos hαle]

end YP3DR


open YieldPostpone.Interplay

namespace YP3DR
open YP3L2

lemma reg2_q (P : Params) (hP : P.Valid) (x : ℝ) (h1 : P.b * x < P.a * μ P)
    (h2 : P.a * (μ P - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * x) :
    0 < (P.a * μ P - P.b * x) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
    (P.a * μ P - P.b * x) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.a / 2 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  refine ⟨div_pos (by linarith) (by positivity), ?_⟩
  rw [div_le_iff₀ (by positivity)]
  nlinarith

set_option maxHeartbeats 1000000 in
/-- Full DR characterization: existence for every cost, and the equilibrium outcome on
`c < c^DR_1`, on `c^DR_1 < c < c^DR_2`, and on `c^DR_2 ≤ c`. -/
theorem dr_full (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .DR σ) ∧
      ∀ σ : Profile, IsSPE P c .DR σ →
        (c < cDR1 P →
          piR P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (16 * P.b * P.α ^ 2) ∧
          piS P c .DR σ = (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2) ∧
          CS P c .DR σ = (P.b * c - P.a * P.α) ^ 2 / (32 * P.b * P.α ^ 2)) ∧
        (cDR1 P < c → c < cDR2 P →
          piR P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (4 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .DR σ = μ P * P.θ * c * (P.a * P.α * (1 - P.θ) - P.b * c) /
              (2 * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .DR σ = μ P ^ 2 * (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (8 * P.b * P.α ^ 2 * (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
        (cDR2 P ≤ c →
          piR P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .DR σ = (P.a * μ P - P.b * c) ^ 2 /
              (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  intro c hc hcμ'
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  have hu0 : 0 < P.α * (1 - P.θ) := by positivity
  have hs2 : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hcμ : P.b * c < P.a * μ P := by rwa [lt_div_iff₀ hb, mul_comm] at hcμ'
  refine ⟨?_, fun σ hσ => ?_⟩
  · rcases le_or_gt c (cDR1 P) with h1 | h1
    · obtain ⟨hadm, -, hval, hle, -⟩ := caseA P hP hα c hc hcμ h1
      exact ⟨_, prof_spe P hP c hc _ hadm (fun w' hw' => hval ▸ hle w' hw')⟩
    · rcases lt_or_ge c (cDR2 P) with h2 | h2
      · obtain ⟨hadm, -, -, hval, hle⟩ := caseB P hP hα c hc hcμ h1 h2
        exact ⟨_, prof_spe P hP c hc _ hadm (fun w' hw' => hval ▸ (hle w' hw').1)⟩
      · obtain ⟨hadm, -, -, hval, hle⟩ := caseC P hP hα c hc hcμ h2
        exact ⟨_, prof_spe P hP c hc _ hadm (fun w' hw' => hval ▸ (hle w' hw').1)⟩
  obtain ⟨hwσ, hmax, hq, hQ, hSV⟩ := spe_char P hP c hc σ hσ
  have hpr := hσ.2.1 rfl
  obtain ⟨hwσ1, hwσ2⟩ := (wAdm_DR P c σ.w).mp hwσ
  have hw0 : 0 < σ.w := lt_trans (div_pos hc hμ0) hwσ1
  have hwa : P.b * σ.w < P.a := by rwa [lt_div_iff₀ hb, mul_comm] at hwσ2
  have hpiS : piS P c .DR σ = Sf P c σ.w := hSV
  refine ⟨fun h1 => ?_, fun h1 h2 => ?_, fun h2 => ?_⟩
  · -- Case A
    obtain ⟨hadm, hinfl, hval, hle, huniq⟩ := caseA P hP hα c hc hcμ h1.le
    have hge := hmax _ hadm
    rw [hval] at hge
    have heq : σ.w = (P.a / P.b + c / P.α) / 2 :=
      huniq h1 σ.w hwσ (le_antisymm (hle σ.w hwσ) hge)
    have hinfl' : c < P.α * (1 - P.θ) * σ.w := by rw [heq]; exact hinfl
    have hq' : σ.q σ.w = (P.a - P.b * σ.w) / 2 := by
      rw [hq]; unfold qpol; rw [if_neg (not_le.mpr hinfl')]
    have hQ' : σ.Q σ.w (σ.q σ.w) = σ.q σ.w / P.α := by
      rw [hQ]; unfold Qpol; rw [if_neg (not_le.mpr hinfl')]
    obtain ⟨hR, hC⟩ := outcome_infl P hP c σ hpr hQ' hq' hw0 hwa
    refine ⟨?_, ?_, ?_⟩
    · rw [hR, heq]; field_simp; ring
    · rw [hpiS, heq, hval]; ring
    · rw [hC, heq]; field_simp; ring
  · -- Case B
    obtain ⟨hadm, hlow0, hreg, hval, hle⟩ := caseB P hP hα c hc hcμ h1 h2
    have hge := hmax _ hadm
    rw [hval] at hge
    have heq : σ.w = c / (P.α * (1 - P.θ)) := (hle σ.w hwσ).2 (le_antisymm (hle σ.w hwσ).1 hge)
    have hlow : P.α * (1 - P.θ) * σ.w ≤ c := by rw [heq]; exact hlow0
    have hxa : P.b * (μ P * σ.w) < P.a * μ P := by nlinarith
    rw [← heq] at hreg
    have hq' : σ.q σ.w = (P.a * μ P - P.b * (μ P * σ.w)) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
      rw [hq]; unfold qpol; rw [if_pos hlow, qs_reg2 P _ hxa hreg]
    have hQ' : σ.Q σ.w (σ.q σ.w) = σ.q σ.w := by
      rw [hQ]; unfold Qpol; rw [if_pos hlow]
    obtain ⟨hpos, hle2⟩ := reg2_q P hP _ hxa hreg
    rw [← hq'] at hpos hle2
    obtain ⟨hR, hC⟩ := outcome_noinfl P hP c σ hpr hQ' hpos hle2
    refine ⟨?_, ?_, ?_⟩
    · rw [hR, hq', heq, hμ]; field_simp; ring
    · rw [hpiS, heq, hval]
    · rw [hC, hq', heq, hμ]; field_simp; ring
  · -- Case C
    obtain ⟨hadm, hlow0, hμw2, hval, hle⟩ := caseC P hP hα c hc hcμ h2
    have hge := hmax _ hadm
    rw [hval] at hge
    have heq : σ.w = (P.a * μ P + P.b * c) / (2 * P.b * μ P) :=
      (hle σ.w hwσ).2 (le_antisymm (hle σ.w hwσ).1 hge)
    have hlow : P.α * (1 - P.θ) * σ.w ≤ c := by rw [heq]; exact hlow0
    have hOR : cOR P ≤ c := by
      have := (basics P hP hα).1; linarith
    obtain ⟨-, -, s3, s4, s5, -, -⟩ := sup2 P hP c hc hcμ hOR ((P.a * μ P + P.b * c) / (2 * P.b)) rfl
    rw [← hμw2, ← heq] at s3 s4 s5
    have hq' : σ.q σ.w = (P.a * μ P - P.b * c) / (4 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
      rw [hq]; unfold qpol; rw [if_pos hlow, s5]
    have hQ' : σ.Q σ.w (σ.q σ.w) = σ.q σ.w := by
      rw [hQ]; unfold Qpol; rw [if_pos hlow]
    obtain ⟨hpos, hle2⟩ := reg2_q P hP _ s3 s4
    rw [qs_reg2 P _ s3 s4] at s5
    rw [s5, ← hq'] at hpos hle2
    obtain ⟨hR, hC⟩ := outcome_noinfl P hP c σ hpr hQ' hpos hle2
    refine ⟨?_, ?_, ?_⟩
    · rw [hR, hq', heq, hμ]; field_simp; ring
    · rw [hpiS, heq, hval]
    · rw [hC, hq', hμ]; field_simp; ring

end YP3DR


open YP3DR in
theorem solution (P : Params) (hP : P.Valid) (hα : 9 / 16 ≤ P.α) :
    ∀ σ : Profile, IsSPE P (cDR2 P) .DR σ →
      piR P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      piS P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
      CS P (cDR2 P) .DR σ = (P.a * μ P - P.b * cDR2 P) ^ 2 /
          (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  intro σ hσ
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < μ P := by rw [hμ]; positivity
  obtain ⟨-, -, hc0, -, e2⟩ := basics P hP hα
  have hlt : cDR2 P < P.a * μ P / P.b := by
    rw [lt_div_iff₀ hb]
    have h1 : P.a * (P.α * (1 - P.θ)) * μ P < P.a * μ P * (μ P + P.θ) := by
      have : P.α * (1 - P.θ) < μ P + P.θ := by rw [hμ]; linarith
      have := mul_lt_mul_of_pos_left this (mul_pos ha hμ0)
      linarith
    have h2 : P.b * cDR2 P * (μ P + P.θ) < P.a * μ P * (μ P + P.θ) := by rw [e2]; exact h1
    have h3 : P.b * cDR2 P < P.a * μ P := lt_of_mul_lt_mul_right h2 (by positivity)
    linarith
  exact ((dr_full P hP hα (cDR2 P) hc0 hlt).2 σ hσ).2.2 le_rfl
