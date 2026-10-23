-- Prove2me | solution 1 for YieldPostpone.Interplay.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T03:10:23.265259+00:00
-- url     : https://prove2.me/submissions/0e455384-c316-4043-9106-aa2213d6a29f

import Mathlib
import Definitions.Def_YieldPostpone_Interplay_Setting
import Theorems.Thm_YieldPostpone_Interplay_eq_5

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

open YP3L2

set_option maxHeartbeats 1000000 in
theorem solution (P : Params) (hP : P.Valid) :
    cOR P < P.a * μ P / P.b ∧
    ∀ c : ℝ, 0 < c → c < P.a * μ P / P.b →
      (∃ σ : Profile, IsSPE P c .OR σ) ∧
      ∀ σ : Profile, IsSPE P c .OR σ →
        (c < max 0 (cOR P) →
          piR P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (16 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (4 * P.b) ∧
          piS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (8 * P.b * P.α ^ 2 * (1 - P.θ)) ∧
          CS P c .OR σ = (P.a * P.α * (1 - P.θ) - P.b * c) ^ 2 /
              (32 * P.b * P.α ^ 2 * (1 - P.θ)) + P.a ^ 2 * P.θ / (8 * P.b)) ∧
        (max 0 (cOR P) < c →
          piR P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (16 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          piS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧
          CS P c .OR σ = (P.a * μ P - P.b * c) ^ 2 /
              (32 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : μ P = P.α * (1 - P.θ) + P.θ := rfl
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  obtain ⟨_, hρα, _⟩ := rho_facts P hP
  have hm := cOR_mul P hP
  refine ⟨?_, ?_⟩
  · rw [lt_div_iff₀ hb, mul_comm, hm, hμ]
    have : 0 < P.a * (P.α * (1 - P.θ)) := by positivity
    nlinarith
  intro c hc hcμ'
  have hcμ : P.b * c < P.a * μ P := by rw [lt_div_iff₀ hb] at hcμ'; linarith
  set w2 := (P.a * μ P + P.b * c) / (2 * P.b) with hw2
  set w3 := (P.a * (P.α * (1 - P.θ)) + P.b * c) / (2 * P.b) with hw3
  constructor
  · -- existence
    let ws := if c < cOR P then w3 else w2
    let σ0 : Profile := ⟨ws, fun _ q => q, fun w => qs P w, fun _ => P.a / (2 * P.b), fun _ _ x => prf P x⟩
    refine ⟨σ0, ?_, ?_, ?_, ?_⟩
    · intro w q _ _
      exact ⟨fun h => absurd h (by decide), fun _ => rfl⟩
    · intro _ w q x hx; exact prf_opt P hP x hx
    · intro w hw
      obtain ⟨hw1, hw2'⟩ := (wAdm_OR P c w).mp hw
      obtain ⟨h0, hlt⟩ := br P hP w (by linarith)
      refine ⟨h0, fun h => absurd h (by decide), ?_⟩
      intro q' p' hq' _
      have hpr : ∀ w q x : ℝ, 0 ≤ x →
          pAdm P (σ0.pr w q x) ∧ ∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P (σ0.pr w q x) x :=
        fun w q x hx => prf_opt P hP x hx
      rw [retailerProfit_eq P hP σ0 hpr w q' p' rfl hq', retailerProfit_eq P hP σ0 hpr w _ _ rfl h0]
      by_cases he : q' = qs P w
      · rw [he]
      · exact (hlt q' hq' he).le
    · have hQ : ∀ w q, σ0.Q w q = q := fun _ _ => rfl
      have hV : ∀ w, supplierValue P c .OR σ0 w = Vf P c w := by
        intro w; rw [supplierValue_eq P c σ0 hQ w]; rfl
      by_cases hcase : c < cOR P
      · obtain ⟨h1, h2, _, _, _, hmax⟩ := sup3 P hP c hc hcμ hcase w3 hw3
        have hws : σ0.w = w3 := by show ws = w3; simp [ws, hcase]
        refine ⟨by rw [hws]; exact (wAdm_OR P c w3).mpr ⟨h1, h2⟩, ?_⟩
        intro w' hw'
        obtain ⟨hw1, hw2'⟩ := (wAdm_OR P c w').mp hw'
        rw [hV, hV, hws]
        by_cases he : w' = w3
        · rw [he]
        · exact (hmax w' hw1 hw2' he).le
      · push Not at hcase
        obtain ⟨h1, h2, _, _, _, _, hmax⟩ := sup2 P hP c hc hcμ hcase w2 hw2
        have hws : σ0.w = w2 := by show ws = w2; simp [ws, not_lt.mpr hcase]
        refine ⟨by rw [hws]; exact (wAdm_OR P c w2).mpr ⟨h1, h2⟩, ?_⟩
        intro w' hw'
        obtain ⟨hw1, hw2'⟩ := (wAdm_OR P c w').mp hw'
        rw [hV, hV, hws]
        exact (hmax w' hw1 hw2').1
  · intro σ hσ
    obtain ⟨hQ, hpr, hq, hw1, hw2', hopt⟩ := spe_facts P hP c hc σ hσ
    have hpiR : piR P c .OR σ = Pi P σ.w (qs P σ.w) := by
      unfold piR
      have h0 := (br P hP σ.w (by linarith)).1
      rw [hq σ.w hw1 hw2', retailerProfit_eq P hP σ hpr σ.w _ _ (hQ σ.w _ hw1 hw2' h0) h0]
    have hpiS : piS P c .OR σ = Vf P c σ.w := by
      unfold piS supplierValue supplierProfit E transfer Vf
      have h0 := (br P hP σ.w (by linarith)).1
      rw [hq σ.w hw1 hw2', hQ σ.w _ hw1 hw2' h0]
      simp [Scenario.byDelivery]; ring
    have hCS : 0 < qs P σ.w → CS P c .OR σ = P.θ * Sv P (qs P σ.w) + (1 - P.θ) * Sv P (P.α * qs P σ.w) := by
      intro hpos
      unfold CS E
      have h0 := hpos.le
      simp only [Scenario.responsive, if_true, delivered]
      rw [hq σ.w hw1 hw2', hQ σ.w _ hw1 hw2' h0]
      have e1 : min (1 * qs P σ.w) (qs P σ.w) = qs P σ.w := by simp
      have e2 : min (P.α * qs P σ.w) (qs P σ.w) = P.α * qs P σ.w := min_eq_left (by nlinarith)
      rw [e1, e2]
      have hαq : 0 < P.α * qs P σ.w := by positivity
      rw [surplus_opt P hP _ hpos _ (hpr _ _ _ h0).1 (hpr _ _ _ h0).2,
        surplus_opt P hP _ hαq _ (hpr _ _ _ hαq.le).1 (hpr _ _ _ hαq.le).2]
    constructor
    · -- inflated piece
      intro hlt
      have hcOR : c < cOR P := by
        rcases le_total 0 (cOR P) with h' | h'
        · rwa [max_eq_right h'] at hlt
        · rw [max_eq_left h'] at hlt; linarith
      obtain ⟨h1, h2, hr3, hqv, hVv, hmax⟩ := sup3 P hP c hc hcμ hcOR w3 hw3
      have hw : σ.w = w3 := by
        by_contra hne
        have := hmax σ.w hw1 hw2' hne
        have := hopt w3 h1 h2
        linarith
      rw [hw] at hpiR hpiS hCS
      have hbw3 : P.b * w3 = (P.a * (P.α * (1 - P.θ)) + P.b * c) / 2 := by rw [hw3]; field_simp
      have hpos : 0 < P.a * (P.α * (1 - P.θ)) - P.b * c := by
        have : 0 < P.a * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
        rw [hμ] at hr3; nlinarith
      set q3 := qs P w3 with hq3
      have hq3a : P.a / 2 < q3 := by
        rw [hqv, lt_div_iff₀ (by positivity)]
        rw [hμ] at hr3; nlinarith
      have hq3b : P.α * q3 ≤ P.a / 2 := by
        rw [hqv, ← mul_div_assoc, div_le_iff₀ (by positivity)]
        have e : P.a / 2 * (4 * (P.α ^ 2 * (1 - P.θ))) - P.α * (P.a * (P.α * (1 - P.θ)) - P.b * c)
            = P.a * P.α ^ 2 * (1 - P.θ) + P.α * (P.b * c) := by ring
        have : 0 ≤ P.a * P.α ^ 2 * (1 - P.θ) + P.α * (P.b * c) := by positivity
        linarith
      refine ⟨?_, ?_, ?_⟩
      · rw [hpiR]
        rw [← mul_right_inj' hb.ne', bPi, bRv_gt P hb q3 hq3a, bRv_le P hb _ hq3b, hbw3, hqv]
        field_simp; ring
      · rw [hpiS, hVv]; field_simp
      · rw [hCS (by linarith)]
        unfold Sv
        rw [if_neg (not_le.mpr hq3a), if_pos hq3b, hqv]
        field_simp; ring
    · -- non-inflated piece
      intro hgt
      have hcOR : cOR P < c := lt_of_le_of_lt (le_max_right _ _) hgt
      obtain ⟨h1, h2, hr1, hr2, hqv, hVv, hmax⟩ := sup2 P hP c hc hcμ hcOR.le w2 hw2
      have hw : σ.w = w2 := by
        by_contra hne
        have := (hmax σ.w hw1 hw2').2 hcOR hne
        have := hopt w2 h1 h2
        linarith
      rw [hw] at hpiR hpiS hCS
      have hbw2 : P.b * w2 = (P.a * μ P + P.b * c) / 2 := by rw [hw2]; field_simp
      set q2 := qs P w2 with hq2
      have hq2pos : 0 < q2 := by rw [hqv]; apply div_pos (by linarith) (by positivity)
      have hq2a : q2 ≤ P.a / 2 := by
        rw [hqv, div_le_iff₀ (by positivity)]; nlinarith
      have hq2b : P.α * q2 ≤ P.a / 2 := by nlinarith
      refine ⟨?_, ?_, ?_⟩
      · rw [hpiR]
        rw [← mul_right_inj' hb.ne', bPi, bRv_le P hb q2 hq2a, bRv_le P hb _ hq2b, hbw2, hqv, hμ]
        field_simp; ring
      · rw [hpiS, hVv]
      · rw [hCS hq2pos]
        unfold Sv
        rw [if_pos hq2a, if_pos hq2b, hqv]
        field_simp; ring
