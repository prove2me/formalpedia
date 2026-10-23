-- Prove2me | solution 1 for YieldPostpone.Payment.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T04:07:18.717453+00:00
-- url     : https://prove2.me/submissions/b4428c53-bfab-4d5a-9201-d6fa97b31a93

import Definitions.Def_YieldPostpone_Payment_ClosedForms

open YieldPostpone.Payment

theorem PPL4_ll_ra {a b x p : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) (hxa : x < a / 2) (hp : 0 < p) :
    p * min (a - b * p) x ≤ ((a - x) / b) * x ∧
      (p * min (a - b * p) x = ((a - x) / b) * x → p = (a - x) / b) := by
  have hps : b * ((a - x) / b) = a - x := by field_simp
  have hpos : 0 < (a - x) / b := div_pos (by linarith) hb
  rcases le_or_gt p ((a - x) / b) with h | h
  · have hmin : a - b * p ≥ x := by nlinarith
    rw [min_eq_right hmin]
    refine ⟨by nlinarith, fun e => ?_⟩
    have : p * x = ((a - x) / b) * x := e
    exact mul_right_cancel₀ hx.ne' this
  · have hmin : a - b * p < x := by nlinarith
    rw [min_eq_left hmin.le]
    have key : p * (a - b * p) < ((a - x) / b) * x := by
      have h1 : a - b * (((a - x) / b) + p) < 0 := by nlinarith
      nlinarith
    exact ⟨key.le, fun e => absurd e key.ne⟩

theorem PPL4_ll_rb {a b x p : ℝ} (ha : 0 < a) (hb : 0 < b) (hxa : a / 2 ≤ x) :
    p * min (a - b * p) x ≤ (a / (2 * b)) * (a / 2) ∧
      (0 < p → p * min (a - b * p) x = (a / (2 * b)) * (a / 2) → p = a / (2 * b)) := by
  have e : (a / (2 * b)) * (a / 2) = a ^ 2 / (4 * b) := by field_simp; ring
  rw [e]
  have h4 : 4 * b * (p * (a - b * p)) ≤ a ^ 2 := by nlinarith [sq_nonneg (a - 2 * b * p)]
  have hle : a ^ 2 / (4 * b) ≥ p * (a - b * p) := by
    rw [ge_iff_le, le_div_iff₀ (by positivity)]; linarith
  refine ⟨?_, fun hp e2 => ?_⟩
  · rcases le_or_gt p 0 with hp | hp
    · have : min (a - b * p) x ≥ 0 ∨ True := Or.inr trivial
      have hm : 0 ≤ min (a - b * p) x := le_min (by nlinarith) (by linarith)
      have : p * min (a - b * p) x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp hm
      have : 0 ≤ a ^ 2 / (4 * b) := by positivity
      linarith
    · calc p * min (a - b * p) x ≤ p * (a - b * p) :=
            mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
        _ ≤ _ := hle
  · have h5 : p * (a - b * p) ≥ a ^ 2 / (4 * b) := by
      calc a ^ 2 / (4 * b) = p * min (a - b * p) x := e2.symm
        _ ≤ p * (a - b * p) := mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
    have h6 : a ^ 2 ≤ 4 * b * (p * (a - b * p)) := by
      rw [ge_iff_le, div_le_iff₀ (by positivity)] at h5; linarith
    have h7 : (a - 2 * b * p) ^ 2 ≤ 0 := by nlinarith
    have h8 : a - 2 * b * p = 0 := by nlinarith [sq_nonneg (a - 2 * b * p)]
    field_simp
    linarith

theorem PPL4_ll_ra_val {a b x : ℝ} (hb : 0 < b) :
    ((a - x) / b) * min (a - b * ((a - x) / b)) x = ((a - x) / b) * x := by
  have hps : b * ((a - x) / b) = a - x := by field_simp
  rw [hps]; simp

theorem PPL4_ll_rb_val {a b x : ℝ} (hb : 0 < b) (hxa : a / 2 ≤ x) :
    (a / (2 * b)) * min (a - b * (a / (2 * b))) x = (a / (2 * b)) * (a / 2) := by
  have : b * (a / (2 * b)) = a / 2 := by field_simp
  rw [this]
  have : a - a / 2 = a / 2 := by ring
  rw [this, min_eq_left hxa]

theorem PPL4_eq_5 (P : Params) (hP : P.Valid) (x : ℝ) :
    (0 < x → x < P.a / 2 →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = (P.a - x) / P.b)) ∧
    (P.a / 2 ≤ x →
      ∀ p : ℝ, pAdm P p →
        ((∀ p' : ℝ, pAdm P p' → salesRev P p' x ≤ salesRev P p x) ↔ p = P.a / (2 * P.b))) := by
  obtain ⟨ha, hb, -, -, -, -⟩ := hP
  have hsr : ∀ q y : ℝ, salesRev P q y = q * min (P.a - P.b * q) y := fun q y => rfl
  constructor
  · intro hx hxa p hp
    have hps : pAdm P ((P.a - x) / P.b) := by
      refine ⟨div_pos (by linarith) hb, ?_⟩
      exact div_lt_div_of_pos_right (by linarith) hb
    constructor
    · intro hmax
      have h1 := hmax _ hps
      rw [hsr, hsr, PPL4_ll_ra_val hb] at h1
      have h2 := (PPL4_ll_ra ha hb hx hxa hp.1)
      exact h2.2 (le_antisymm h2.1 h1)
    · rintro rfl
      intro p' hp'
      rw [hsr, hsr, PPL4_ll_ra_val hb]
      exact (PPL4_ll_ra ha hb hx hxa hp'.1).1
  · intro hxa' p hp
    have hps : pAdm P (P.a / (2 * P.b)) := by
      refine ⟨by positivity, ?_⟩
      exact (div_lt_div_iff₀ (by positivity) hb).2 (by nlinarith)
    constructor
    · intro hmax
      have h1 := hmax _ hps
      rw [hsr, hsr, PPL4_ll_rb_val hb hxa'] at h1
      have h2 := (PPL4_ll_rb (p := p) (x := x) ha hb hxa')
      exact h2.2 hp.1 (le_antisymm h2.1 h1)
    · rintro rfl
      intro p' hp'
      rw [hsr, hsr, PPL4_ll_rb_val hb hxa']
      exact (PPL4_ll_rb ha hb hxa').1



namespace PPL4

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
    · have := ((PPL4_eq_5 P hP x).1 hx h2 p ⟨hp0, hp1⟩).mp hopt
      rw [Rv_le P x h2.le, this]
      unfold salesRev demand
      have : P.a - P.b * ((P.a - x) / P.b) = x := by field_simp; ring
      rw [this, min_self]; ring
    · have := ((PPL4_eq_5 P hP x).2 h2 p ⟨hp0, hp1⟩).mp hopt
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

lemma bRv_le (P : Params) (hb : 0 < P.b) (x : ℝ) (h : x ≤ P.a / 2) : P.b * Rv P x = x * (P.a - x) := by
  rw [Rv_le P x h]; field_simp

lemma bRv_gt (P : Params) (hb : 0 < P.b) (x : ℝ) (h : P.a / 2 < x) : P.b * Rv P x = P.a ^ 2 / 4 := by
  rw [Rv_gt P x h]; field_simp

lemma bPi (P : Params) (w q : ℝ) :
    P.b * Pi P w q = P.θ * (P.b * Rv P q) + (1 - P.θ) * (P.b * Rv P (P.α * q)) - (P.b * w) * q := by
  unfold Pi; ring

/-- region I: no order -/
lemma reg1 (P : Params) (hP : P.Valid) (w : ℝ) (hw : P.a * P.μ ≤ P.b * w) (q : ℝ) (hq : 0 < q) :
    Pi P w q < Pi P w 0 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
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
    (hw : P.b * w = P.a * P.μ - 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * q0) (q : ℝ) (hq : 0 ≤ q) (hne : q ≠ q0) :
    Pi P w q < Pi P w q0 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hθ' : 0 < 1 - P.θ := by linarith
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
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
  if P.a * P.μ ≤ P.b * w then 0
  else if P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w then
    (P.a * P.μ - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))
  else (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ)))

lemma br (P : Params) (hP : P.Valid) (w : ℝ) (hw : 0 < w) :
    0 ≤ qs P w ∧ ∀ q : ℝ, 0 ≤ q → q ≠ qs P w → Pi P w q < Pi P w (qs P w) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hθ' : 0 < 1 - P.θ := by linarith
  have hs : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hk : 0 < P.α ^ 2 * (1 - P.θ) := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
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

lemma qs_reg1 (P : Params) (w : ℝ) (h1 : P.a * P.μ ≤ P.b * w) : qs P w = 0 := by
  unfold qs; rw [if_pos h1]

lemma qs_reg2 (P : Params) (w : ℝ) (h1 : P.b * w < P.a * P.μ)
    (h2 : P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * w) :
    qs P w = (P.a * P.μ - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  unfold qs; rw [if_neg (not_le.mpr h1), if_pos h2]

lemma qs_reg3 (P : Params) (w : ℝ) (h1 : P.b * w < P.a * P.μ)
    (h2 : P.b * w < P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ))) :
    qs P w = (P.a * (P.α * (1 - P.θ)) - P.b * w) / (2 * (P.α ^ 2 * (1 - P.θ))) := by
  unfold qs; rw [if_neg (not_le.mpr h1), if_neg (not_le.mpr h2)]

/-- the supplier's value of posting `w` (pay-by-order, retailer best-responds) -/
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
  · have := ((PPL4_eq_5 P hP x).1 hx h2 p hp).mp hopt
    subst this
    have hd : demand P ((P.a - x) / P.b) = x := by unfold demand; field_simp; ring
    unfold Sv; rw [hd, min_self, if_pos h2.le]; field_simp; ring
  · have := ((PPL4_eq_5 P hP x).2 h2 p hp).mp hopt
    subst this
    have hd : demand P (P.a / (2 * P.b)) = P.a / 2 := by unfold demand; field_simp; ring
    rw [hd, min_eq_left h2]
    unfold Sv
    split_ifs with h3
    · have : x = P.a / 2 := le_antisymm h3 h2
      subst this; field_simp; ring
    · field_simp; ring

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
    exact ⟨hadm, ((PPL4_eq_5 P hP x).1 h1 h2 _ hadm).mpr rfl⟩
  · refine ⟨hadm2, ?_⟩
    rcases hx.lt_or_eq with hx | hx
    · have h2 : P.a / 2 ≤ x := by
        by_contra hc; push Not at hc; exact h ⟨hx, hc⟩
      exact ((PPL4_eq_5 P hP x).2 h2 _ hadm2).mpr rfl
    · subst hx
      intro p' hp'
      have hz : ∀ p, pAdm P p → salesRev P p 0 = 0 := by
        intro p hp
        obtain ⟨_, hp1⟩ := hp
        unfold salesRev demand
        rw [lt_div_iff₀ hb] at hp1
        rw [min_eq_right (by linarith)]; ring
      rw [hz p' hp', hz _ hadm2]


end PPL4

namespace PPL4

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

end PPL4

lemma PPL4_rto_poly (α θ : ℝ) (hα : (9 : ℝ) / 16 ≤ α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    (1 - α) * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) <
      (1 + α) * ((α * (1 - θ) + θ) ^ 2 + θ -
        θ * (α * (α * (1 - θ) + θ) + (1 - α) * (1 - θ))) := by
  have hg : 0 < (1 - θ) * (3 * α + 1) * (2 * α - 1) + θ * (2 * α - 1) * (α + 2) +
      (1 - α ^ 2) * θ * (1 - θ) := by
    have h2 : 0 < 2 * α - 1 := by linarith
    have h3 : 0 < 1 - α ^ 2 := by nlinarith
    have h4 : 0 < 1 - θ := by linarith
    positivity
  have hid : (1 + α) * ((α * (1 - θ) + θ) ^ 2 + θ -
        θ * (α * (α * (1 - θ) + θ) + (1 - α) * (1 - θ))) -
      (1 - α) * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) =
      2 * α ^ 3 + (1 - α) * θ * ((1 - θ) * (3 * α + 1) * (2 * α - 1) +
        θ * (2 * α - 1) * (α + 2) + (1 - α ^ 2) * θ * (1 - θ)) := by ring
  have h1 : 0 < 1 - α := by linarith
  have hα0 : 0 < α := by linarith
  have : 0 < 2 * α ^ 3 + (1 - α) * θ * ((1 - θ) * (3 * α + 1) * (2 * α - 1) +
        θ * (2 * α - 1) * (α + 2) + (1 - α ^ 2) * θ * (1 - θ)) := by positivity
  linarith

lemma PPL4_rto_main (a b α θ : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : (9 : ℝ) / 16 ≤ α)
    (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (μ : ℝ) (hμ : μ = α * (1 - θ) + θ) :
    (a / b) * α * (1 - θ) * ((1 - α) - Real.sqrt (α ^ 2 + θ / (1 - θ))) < 0 ∧
    0 < a * α * (1 - Real.sqrt (α ^ 2 * (1 - θ) + θ)) / (b * (1 + α)) ∧
    a * α * (1 - Real.sqrt (α ^ 2 * (1 - θ) + θ)) / (b * (1 + α)) <
      a * α * (1 - θ) *
        (μ ^ 2 + θ - 2 * θ * Real.sqrt (α * μ * (1 - α) * (1 - θ))) /
        (b * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) ∧
    a * α * (1 - θ) *
        (μ ^ 2 + θ - 2 * θ * Real.sqrt (α * μ * (1 - α) * (1 - θ))) /
        (b * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)) <
      a * α * μ * (1 - θ) / (b * (μ + θ)) := by
  have hα0 : 0 < α := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hμpos : 0 < μ := by rw [hμ]; positivity
  have hNpos : 0 < α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 := by
    positivity
  set N := α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2 with hN
  set r := Real.sqrt (α * μ * (1 - α) * (1 - θ)) with hr
  set u := Real.sqrt (α ^ 2 * (1 - θ) + θ) with hu
  clear_value N r u
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hs : α ≤ Real.sqrt (α ^ 2 + θ / (1 - θ)) := by
      rw [Real.le_sqrt (by linarith) (by positivity)]
      have : 0 ≤ θ / (1 - θ) := by positivity
      linarith
    have hneg : (1 - α) - Real.sqrt (α ^ 2 + θ / (1 - θ)) < 0 := by linarith
    have hpos : 0 < a / b * α * (1 - θ) := by positivity
    exact mul_neg_of_pos_of_neg hpos hneg
  · have hD : α ^ 2 * (1 - θ) + θ < 1 := by
      nlinarith [mul_pos h1θ (show 0 < 1 - α ^ 2 by nlinarith)]
    have hs : u < 1 := by
      rw [hu, Real.sqrt_lt' (by norm_num)]; linarith
    have : 0 < 1 - u := by linarith
    positivity
  · have hu_ge : μ ≤ u := by
      rw [hu, Real.le_sqrt hμpos.le (by positivity), hμ]
      have : 0 ≤ θ * (1 - θ) * (1 - α) ^ 2 := by positivity
      nlinarith
    have hr_le : 2 * r ≤ α * μ + (1 - α) * (1 - θ) := by
      have : r ≤ (α * μ + (1 - α) * (1 - θ)) / 2 := by
        rw [hr, Real.sqrt_le_left]
        · nlinarith [sq_nonneg (α * μ - (1 - α) * (1 - θ))]
        · positivity
      linarith
    have hpoly := PPL4_rto_poly α θ hα hα1 hθ0 hθ1
    rw [← hμ, ← hN] at hpoly
    have h1 : a * α * (1 - u) / (b * (1 + α)) ≤ a * α * (1 - μ) / (b * (1 + α)) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have : 0 < a * α := by positivity
      nlinarith
    have h2 : a * α * (1 - θ) * (μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ))) / (b * N) ≤
        a * α * (1 - θ) * (μ ^ 2 + θ - 2 * θ * r) / (b * N) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hk : 0 < a * α * (1 - θ) := by positivity
      have h3 : θ * (2 * r) ≤ θ * (α * μ + (1 - α) * (1 - θ)) :=
        mul_le_mul_of_nonneg_left hr_le hθ0.le
      have h4 : μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ)) ≤ μ ^ 2 + θ - 2 * θ * r := by
        linarith
      exact mul_le_mul_of_nonneg_left h4 hk.le
    have h3 : a * α * (1 - μ) / (b * (1 + α)) <
        a * α * (1 - θ) * (μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ))) / (b * N) := by
      rw [div_lt_div_iff₀ (by positivity) (by positivity)]
      have h1μ : 1 - μ = (1 - α) * (1 - θ) := by rw [hμ]; ring
      rw [h1μ]
      have hk : 0 < a * α * (1 - θ) * b := by positivity
      have := mul_lt_mul_of_pos_left hpoly hk
      linarith
    linarith
  · have hR2 : 0 < α * μ * (1 - α) * (1 - θ) := by positivity
    have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hR2
    have hrsq : r ^ 2 = α * μ * (1 - α) * (1 - θ) := by rw [hr]; exact Real.sq_sqrt hR2.le
    set E := θ * (1 - α) * (1 - θ) * (θ ^ 2 + θ - α ^ 2 * (1 - θ) ^ 2) with hE
    clear_value E
    have hEid : (μ ^ 2 + θ) * (μ + θ) - μ * N = E := by rw [hμ, hN, hE]; ring
    have hcore : E < 2 * θ * (μ + θ) * r := by
      have hrhs : 0 < 2 * θ * (μ + θ) * r := by positivity
      by_cases hE0 : E ≤ 0
      · linarith
      · push Not at hE0
        have hK : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) +
            α * θ * (5 - θ) - θ * (1 - θ) := by
          have h6 : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) := by positivity
          have h7 : α * θ * (5 - θ) - θ * (1 - θ) = θ * (α * (5 - θ) - (1 - θ)) := by ring
          have h8 : 0 < θ * (α * (5 - θ) - (1 - θ)) := by
            apply mul_pos hθ0; nlinarith
          linarith
        have hG : (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 =
            θ ^ 2 * (1 - α) * (1 - θ) * N *
              (α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) +
                α * θ * (5 - θ) - θ * (1 - θ)) := by
          rw [mul_pow, hrsq, hE, hN, hμ]; ring
        have hGpos : 0 < (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 := by
          rw [hG]; positivity
        nlinarith
    have hmain : (μ ^ 2 + θ - 2 * θ * r) * (μ + θ) < μ * N := by
      have : (μ ^ 2 + θ - 2 * θ * r) * (μ + θ) = (μ ^ 2 + θ) * (μ + θ) - 2 * θ * (μ + θ) * r := by
        ring
      linarith
    rw [div_lt_div_iff₀ (mul_pos hb hNpos) (mul_pos hb (by linarith : 0 < μ + θ))]
    have hk : 0 < a * α * (1 - θ) * b := by positivity
    have := mul_lt_mul_of_pos_left hmain hk
    linarith



open YieldPostpone.Payment

namespace PPL4

lemma wAdm_DR (P : Params) (c w : ℝ) :
    wAdm P c .DR w ↔ c / P.μ < w ∧ w < P.a / P.b := by
  simp [wAdm, Scenario.byDelivery]

lemma isSPE_DR (P : Params) (c : ℝ) (σ : Profile) :
    IsSPE P c .DR σ ↔
      (∀ w q, wAdm P c .DR w → 0 ≤ q →
        0 ≤ σ.Q w q ∧
        (∀ Q', 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤
          supplierProfit P c .DR w (σ.Q w q) q) ∧
        ((∀ Q', 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤
          supplierProfit P c .DR w q q) → σ.Q w q = q)) ∧
      (∀ w q x : ℝ, 0 ≤ x →
        pAdm P (σ.pr w q x) ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x) ∧
      (∀ w, wAdm P c .DR w →
        0 ≤ σ.q w ∧ True ∧
        ∀ q' p', 0 ≤ q' → True →
          retailerProfit P .DR σ w q' p' ≤ retailerProfit P .DR σ w (σ.q w) (σ.p w)) ∧
      wAdm P c .DR σ.w ∧
      ∀ w', wAdm P c .DR w' → supplierValue P c .DR σ w' ≤ supplierValue P c .DR σ σ.w :=
  Iff.rfl

lemma sp_eqR (P : Params) (c w Q q : ℝ) :
    supplierProfit P c .DR w Q q =
      P.θ * (w * min Q q) + (1 - P.θ) * (w * min (P.α * Q) q) - c * Q := by
  simp [supplierProfit, E, transfer, delivered, Scenario.byDelivery]

lemma wpos (P : Params) (hP : P.Valid) (c w : ℝ) (hc : 0 < c) (hw : wAdm P c .DR w) :
    c < w * (P.α * (1 - P.θ) + P.θ) ∧ 0 < w := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have hμ0 : 0 < P.μ := by
    show 0 < P.α * (1 - P.θ) + P.θ
    have : 0 < 1 - P.θ := by linarith
    positivity
  obtain ⟨hw1, -⟩ := (wAdm_DR P c w).mp hw
  rw [div_lt_iff₀ hμ0] at hw1
  have h : c < w * (P.α * (1 - P.θ) + P.θ) := hw1
  refine ⟨h, ?_⟩
  by_contra hn
  push Not at hn
  have : w * (P.α * (1 - P.θ) + P.θ) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hn (by have : 0 < 1 - P.θ := (by linarith); positivity)
  linarith

/-- production response in scenario DR, from the explicit optimality lemmas -/
lemma prodR (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (w q Q : ℝ)
    (hw : wAdm P c .DR w) (hq : 0 ≤ q)
    (hQ0 : 0 ≤ Q)
    (hQopt : ∀ Q', 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤ supplierProfit P c .DR w Q q)
    (htie : (∀ Q', 0 ≤ Q' → supplierProfit P c .DR w Q' q ≤
          supplierProfit P c .DR w q q) → Q = q) :
    Q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hwμ := (wpos P hP c w hc hw).1
  split_ifs with hlow
  · apply htie
    intro Q' hQ'
    rw [sp_eqR, sp_eqR]
    exact prod_low P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ'
  · push Not at hlow
    have hα : 0 ≤ q / P.α := by positivity
    have h1 := hQopt (q / P.α) hα
    rw [sp_eqR, sp_eqR] at h1
    obtain ⟨h2, h3⟩ := prod_high P.α P.θ c w q Q hα0 hα1 hθ0 hθ1 hc hwμ hlow hq hQ0
    exact h3 (le_antisymm h2 h1)

lemma QcharR (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (w q : ℝ) (hw : wAdm P c .DR w) (hq : 0 ≤ q) :
    σ.Q w q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α := by
  obtain ⟨hQ0, hQopt, htie⟩ := ((isSPE_DR P c σ).mp hσ).1 w q hw hq
  exact prodR P hP c hc w q _ hw hq hQ0 hQopt htie

lemma rp_eqR (P : Params) (σ : Profile) (w q p : ℝ) :
    retailerProfit P .DR σ w q p =
      P.θ * (salesRev P (σ.pr w q (min (σ.Q w q) q)) (min (σ.Q w q) q) -
        w * min (σ.Q w q) q) +
      (1 - P.θ) * (salesRev P (σ.pr w q (min (P.α * σ.Q w q) q)) (min (P.α * σ.Q w q) q) -
        w * min (P.α * σ.Q w q) q) := by
  simp only [retailerProfit, E, transfer, delivered, Scenario.byDelivery, Scenario.responsive,
    if_true, one_mul]

lemma RP_lowR (P : Params) (hP : P.Valid) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w q p : ℝ) (hq : 0 ≤ q) (hQ : σ.Q w q = q) :
    retailerProfit P .DR σ w q p = Pi P (P.μ * w) q := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hαq : P.α * q ≤ q := by nlinarith
  have hαq0 : 0 ≤ P.α * q := by positivity
  rw [rp_eqR, hQ, min_self, min_eq_left hαq,
    rev_opt P hP q hq _ (hpr w q q hq).1 (hpr w q q hq).2,
    rev_opt P hP (P.α * q) hαq0 _ (hpr w q _ hαq0).1 (hpr w q _ hαq0).2]
  unfold Pi
  show _ = _ - (P.α * (1 - P.θ) + P.θ) * w * q
  ring

lemma RP_highR (P : Params) (hP : P.Valid) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w q p : ℝ) (hq : 0 ≤ q) (hQ : σ.Q w q = q / P.α) :
    retailerProfit P .DR σ w q p = Rv P q - w * q := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
  have hαqα : P.α * (q / P.α) = q := by field_simp
  rw [rp_eqR, hQ, min_eq_right hqα, hαqα, min_self,
    rev_opt P hP q hq _ (hpr w q q hq).1 (hpr w q q hq).2]
  ring

/-- the retailer's unique best response when the supplier inflates production -/
lemma brH (P : Params) (hP : P.Valid) (w : ℝ) (hw0 : 0 < w) (hwa : P.b * w < P.a)
    (q : ℝ) (hq : 0 ≤ q) (hne : q ≠ (P.a - P.b * w) / 2) :
    Rv P q - w * q < Rv P ((P.a - P.b * w) / 2) - w * ((P.a - P.b * w) / 2) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hqh : (P.a - P.b * w) / 2 ≤ P.a / 2 := by
    have : 0 < P.b * w := by positivity
    linarith
  rw [← mul_lt_mul_iff_of_pos_left hb, mul_sub, mul_sub, bRv_le P hb _ hqh]
  have hd : 0 < (q - (P.a - P.b * w) / 2) ^ 2 := by
    have : q - (P.a - P.b * w) / 2 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  rcases le_or_gt q (P.a / 2) with h1 | h1
  · rw [bRv_le P hb q h1]
    nlinarith
  · rw [bRv_gt P hb q h1]
    have : 0 < P.b * w := by positivity
    nlinarith

/-- the retailer's best response in scenario DR -/
noncomputable def qR (P : Params) (c w : ℝ) : ℝ :=
  if P.α * (1 - P.θ) * w ≤ c then qs P (P.μ * w) else (P.a - P.b * w) / 2

lemma qR_nonneg (P : Params) (hP : P.Valid) (c w : ℝ) (hc : 0 < c) (hw : wAdm P c .DR w) :
    0 ≤ qR P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hwμ, hw0⟩ := wpos P hP c w hc hw
  obtain ⟨-, hwa⟩ := (wAdm_DR P c w).mp hw
  rw [lt_div_iff₀ hb] at hwa
  unfold qR
  split_ifs
  · exact (br P hP (P.μ * w) (by show 0 < (P.α * (1 - P.θ) + P.θ) * w; nlinarith)).1
  · linarith

/-- retailer optimality in DR given the production rule and optimal ex post prices -/
lemma retR (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P (σ.pr w q x) ∧ ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P (σ.pr w q x) x)
    (w : ℝ) (hw : wAdm P c .DR w)
    (hQ : ∀ q, 0 ≤ q → σ.Q w q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α)
    (q p p' : ℝ) (hq : 0 ≤ q) (hne : q ≠ qR P c w) :
    retailerProfit P .DR σ w q p < retailerProfit P .DR σ w (qR P c w) p' := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hwμ, hw0⟩ := wpos P hP c w hc hw
  obtain ⟨-, hwa⟩ := (wAdm_DR P c w).mp hw
  rw [lt_div_iff₀ hb] at hwa
  have hq0 := qR_nonneg P hP c w hc hw
  have e1 := hQ q hq
  have e2 := hQ _ hq0
  unfold qR at hne hq0 e2 ⊢
  split_ifs at e1 e2 hne hq0 ⊢ with hlow
  · rw [RP_lowR P hP σ hpr w q p hq e1, RP_lowR P hP σ hpr w _ p' hq0 e2]
    exact (br P hP (P.μ * w) (by show 0 < (P.α * (1 - P.θ) + P.θ) * w; nlinarith)).2 q hq hne
  · rw [RP_highR P hP σ hpr w q p hq e1, RP_highR P hP σ hpr w _ p' hq0 e2]
    exact brH P hP w hw0 (by linarith) q hq hne

lemma qR_spe (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (w : ℝ) (hw : wAdm P c .DR w) : σ.q w = qR P c w := by
  obtain ⟨-, hpr, hret, -, -⟩ := (isSPE_DR P c σ).mp hσ
  obtain ⟨hq0, -, hopt⟩ := hret w hw
  by_contra hne
  have h1 := hopt (qR P c w) (σ.p w) (qR_nonneg P hP c w hc hw) trivial
  have h2 := retR P hP c hc σ hpr w hw (fun q hq => QcharR P hP c hc σ hσ w q hw hq)
    (σ.q w) (σ.p w) (σ.p w) hq0 hne
  linarith

/-- the supplier's value of posting `w` in DR -/
noncomputable def Vd (P : Params) (c w : ℝ) : ℝ :=
  if P.α * (1 - P.θ) * w ≤ c then (P.μ * w - c) * qs P (P.μ * w)
  else (w - c / P.α) * ((P.a - P.b * w) / 2)

lemma SV_R (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile) (w : ℝ)
    (hw : wAdm P c .DR w)
    (hQ : ∀ q, 0 ≤ q → σ.Q w q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α)
    (hq : σ.q w = qR P c w) :
    supplierValue P c .DR σ w = Vd P c w := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hq0 := qR_nonneg P hP c w hc hw
  unfold supplierValue
  rw [hq, hQ _ hq0, sp_eqR]
  unfold Vd qR
  split_ifs with hlow
  · have hq0' : 0 ≤ qs P (P.μ * w) := by unfold qR at hq0; rwa [if_pos hlow] at hq0
    have hαq : P.α * qs P (P.μ * w) ≤ qs P (P.μ * w) := by nlinarith
    rw [min_self, min_eq_left hαq]
    show _ = ((P.α * (1 - P.θ) + P.θ) * w - c) * _
    ring
  · have hq0' : 0 ≤ (P.a - P.b * w) / 2 := by unfold qR at hq0; rwa [if_neg hlow] at hq0
    set q := (P.a - P.b * w) / 2
    have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
    have hαqα : P.α * (q / P.α) = q := by field_simp
    rw [min_eq_right hqα, hαqα, min_self]
    field_simp
    ring

end PPL4


open YieldPostpone.Payment

namespace PPL4

lemma G_pos (α θ : ℝ) (hα : (9 : ℝ) / 16 ≤ α) (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    α * (1 - θ) * (1 - α) * (α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2) <
    (α * (1 - θ) + θ) * ((α * (1 - θ) + θ) ^ 2 + θ -
      θ * (α * (α * (1 - θ) + θ) + (1 - α) * (1 - θ))) := by
  obtain ⟨s, rfl⟩ : ∃ s, α = 1 - s := ⟨1 - α, by ring⟩
  have hs0 : 0 < s := by linarith
  have hs1 : s ≤ 7 / 16 := by linarith
  have key : (( 1 - s) * (1 - θ) + θ) * (((1 - s) * (1 - θ) + θ) ^ 2 + θ -
      θ * ((1 - s) * ((1 - s) * (1 - θ) + θ) + (1 - (1 - s)) * (1 - θ))) -
      (1 - s) * (1 - θ) * (1 - (1 - s)) * ((1 - s) ^ 2 * (1 - θ) ^ 3 +
        4 * (1 - s) * θ * (1 - θ) + θ * (1 + θ) ^ 2) =
      (1 - s) ^ 4 + θ ^ 4 * (s ^ 2 * ((1 - s) * (2 - s))) +
      θ ^ 3 * (s * ((1 - 5 / 2 * s) ^ 2 + s ^ 2 * (15 / 4 - 4 * s))) +
      θ ^ 2 * (s * (1 + s * (8 - 15 * s) + 6 * s ^ 3)) +
      θ * (s * ((1 - 2 * s) * ((1 - s) * (3 - 2 * s)))) := by ring
  have t0 : 0 < (1 - s) ^ 4 := by
    have : 0 < 1 - s := by linarith
    positivity
  have t1 : 0 ≤ θ ^ 4 * (s ^ 2 * ((1 - s) * (2 - s))) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg (by positivity)
    apply mul_nonneg <;> linarith
  have t2 : 0 ≤ θ ^ 3 * (s * ((1 - 5 / 2 * s) ^ 2 + s ^ 2 * (15 / 4 - 4 * s))) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg hs0.le
    have : 0 ≤ s ^ 2 * (15 / 4 - 4 * s) := mul_nonneg (by positivity) (by linarith)
    positivity
  have t3 : 0 ≤ θ ^ 2 * (s * (1 + s * (8 - 15 * s) + 6 * s ^ 3)) := by
    apply mul_nonneg (by positivity)
    apply mul_nonneg hs0.le
    have : 0 ≤ s * (8 - 15 * s) := mul_nonneg hs0.le (by linarith)
    positivity
  have t4 : 0 ≤ θ * (s * ((1 - 2 * s) * ((1 - s) * (3 - 2 * s)))) := by
    apply mul_nonneg hθ0.le
    apply mul_nonneg hs0.le
    apply mul_nonneg (by linarith)
    apply mul_nonneg <;> linarith
  linarith

/-- the quadratic whose sign compares `g₂(w₀)` with the high-regime optimum -/
noncomputable def Pf (P : Params) (c : ℝ) : ℝ :=
  4 * P.b * P.μ * P.θ * c * (P.a * (P.α * (1 - P.θ)) - P.b * c) -
    (1 - P.θ) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * (P.a * P.α - P.b * c) ^ 2

lemma g_c2 (a b α θ μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : μ = α * (1 - θ) + θ) :
    b * (1 + θ) * (a * α * μ * (1 - θ) / (b * (μ + θ))) ≤ a * (α * (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have e : b * (1 + θ) * (a * α * μ * (1 - θ) / (b * (μ + θ))) =
      (1 + θ) * (a * α * μ * (1 - θ)) / (μ + θ) := by field_simp
  rw [e, div_le_iff₀ (by positivity)]
  have : 0 ≤ 1 - μ := by rw [hμ]; nlinarith
  have : 0 ≤ a * α * (1 - θ) * θ * (1 - μ) := by positivity
  nlinarith

set_option maxHeartbeats 1000000 in
lemma g_fac (a b α θ μ N r c : ℝ) (hμ : μ = α * (1 - θ) + θ)
    (hN : N = α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)
    (hrsq : r ^ 2 = α * μ * (1 - α) * (1 - θ)) :
    -N * (4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2) =
    (b * N * c - a * (α * (1 - θ)) * (μ ^ 2 + θ)) ^ 2 - (2 * a * (α * (1 - θ)) * θ * r) ^ 2 := by
  have e : (2 * a * (α * (1 - θ)) * θ * r) ^ 2 = 4 * a ^ 2 * (α * (1 - θ)) ^ 2 * θ ^ 2 * r ^ 2 := by
    ring
  rw [e, hrsq, hN, hμ]
  ring

lemma g_r2 (a b α θ μ N r : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : (9 : ℝ) / 16 ≤ α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : μ = α * (1 - θ) + θ)
    (hN : N = α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)
    (hr0 : 0 < r) (hrsq : r ^ 2 = α * μ * (1 - α) * (1 - θ)) :
    b * N * (a * α * μ * (1 - θ) / (b * (μ + θ))) - a * (α * (1 - θ)) * (μ ^ 2 + θ) <
      2 * a * (α * (1 - θ)) * θ * r := by
  have hα0 : 0 < α := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have h1α : 0 < 1 - α := by linarith
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hNpos : 0 < N := by rw [hN]; positivity
  set E := θ * (1 - α) * (1 - θ) * (θ ^ 2 + θ - α ^ 2 * (1 - θ) ^ 2) with hE
  have hEid : (μ ^ 2 + θ) * (μ + θ) - μ * N = E := by rw [hμ, hN, hE]; ring
  have hK : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) +
      α * θ * (5 - θ) - θ * (1 - θ) := by
    have h6 : 0 < α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) := by positivity
    have h8 : 0 < θ * (α * (5 - θ) - (1 - θ)) := by
      apply mul_pos hθ0; nlinarith
    have e : α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) + α * θ * (5 - θ) - θ * (1 - θ) =
      (α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ)) + θ * (α * (5 - θ) - (1 - θ)) := by ring
    rw [e]; linarith
  have hG : (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 =
      θ ^ 2 * (1 - α) * (1 - θ) * N *
        (α ^ 3 * (1 - θ) ^ 2 + α ^ 2 * (1 - θ) * (3 + θ) + α * θ * (5 - θ) - θ * (1 - θ)) := by
    have e : (2 * θ * (μ + θ) * r) ^ 2 = 4 * θ ^ 2 * (μ + θ) ^ 2 * r ^ 2 := by ring
    rw [e, hrsq, hE, hN, hμ]; ring
  have hGpos : 0 < (2 * θ * (μ + θ) * r) ^ 2 - E ^ 2 := by rw [hG]; positivity
  have hR : 0 < 2 * θ * (μ + θ) * r := by positivity
  have hEl : -E < 2 * θ * (μ + θ) * r := by
    by_contra h
    push Not at h
    have h3 := mul_le_mul h h hR.le (by linarith)
    have e : (-E) * (-E) = E ^ 2 := by ring
    rw [e, ← sq] at h3
    linarith
  have hμθ : 0 < μ + θ := by linarith
  have hval : (b * N * (a * α * μ * (1 - θ) / (b * (μ + θ))) - a * (α * (1 - θ)) * (μ ^ 2 + θ)) =
      -(a * (α * (1 - θ))) * E / (μ + θ) := by
    rw [← hEid]
    have e1 : b * N * (a * α * μ * (1 - θ) / (b * (μ + θ))) = a * α * (1 - θ) * (μ * N) / (μ + θ) := by
      field_simp
    rw [e1, eq_div_iff hμθ.ne', sub_mul, div_mul_cancel₀ _ hμθ.ne']
    ring
  rw [hval, div_lt_iff₀ hμθ]
  have hau : 0 < a * (α * (1 - θ)) := by positivity
  have h4 := mul_lt_mul_of_pos_left hEl hau
  have e : (2 * a * (α * (1 - θ)) * θ * r) * (μ + θ) = a * (α * (1 - θ)) * (2 * θ * (μ + θ) * r) := by
    ring
  rw [e]
  linarith

lemma g_F1 (a b α θ μ N r c c1 : ℝ) (ha : 0 < a) (hb : 0 < b) (hα : (9 : ℝ) / 16 ≤ α)
    (hα1 : α < 1) (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : μ = α * (1 - θ) + θ)
    (hN : N = α ^ 2 * (1 - θ) ^ 3 + 4 * α * θ * (1 - θ) + θ * (1 + θ) ^ 2)
    (hr_le : 2 * r ≤ α * μ + (1 - α) * (1 - θ))
    (hc1 : b * N * c1 = a * (α * (1 - θ)) * (μ ^ 2 + θ) - 2 * a * (α * (1 - θ)) * θ * r)
    (hc : c1 < c) :
    a * (α * (1 - θ)) ^ 2 * (1 - α) < b * c * μ := by
  have hα0 : 0 < α := by linarith
  have h1θ : 0 < 1 - θ := by linarith
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have hNpos : 0 < N := by rw [hN]; positivity
  have hG := G_pos α θ hα hα1 hθ0 hθ1
  rw [← hμ, ← hN] at hG
  have hu : 0 < a * (α * (1 - θ)) := by positivity
  have h3 : μ * (μ ^ 2 + θ - θ * (α * μ + (1 - α) * (1 - θ))) ≤ μ * (μ ^ 2 + θ - 2 * θ * r) := by
    apply mul_le_mul_of_nonneg_left _ hμ0.le
    nlinarith
  have h4 : α * (1 - θ) * (1 - α) * N ≤ μ * (μ ^ 2 + θ - 2 * θ * r) := by linarith
  have h5 := mul_le_mul_of_nonneg_left h4 hu.le
  have h1 : a * (α * (1 - θ)) ^ 2 * (1 - α) * N ≤ b * N * c1 * μ := by
    rw [hc1]; nlinarith
  have h2 : b * N * c1 * μ < b * N * c * μ := by
    apply mul_lt_mul_of_pos_right _ hμ0
    exact mul_lt_mul_of_pos_left hc (by positivity)
  have h3 : a * (α * (1 - θ)) ^ 2 * (1 - α) * N < b * c * μ * N := by nlinarith
  exact lt_of_mul_lt_mul_right h3 hNpos.le

lemma g_Ct (a b α θ μ s Ct c : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α) (hα1 : α < 1)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hμ : μ = α * (1 - θ) + θ)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = α ^ 2 * (1 - θ) + θ)
    (hCt : Ct = a * α * (1 - s) / (b * (1 + α))) (hc : Ct < c) (hca : b * c < a * α) :
    (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2 < α ^ 2 * (a * μ - b * c) ^ 2 := by
  have hsα : α < s := by
    have : α ^ 2 < s ^ 2 := by rw [hs2]; nlinarith [mul_pos hθ0 (show 0 < 1 - α ^ 2 by nlinarith)]
    nlinarith
  have hid : s * (a * α - b * c) - α * (a * μ - b * c) = (s - α) * b * (Ct - c) := by
    rw [hCt]; field_simp; rw [hμ]; linear_combination (a * α) * hs2
  have hlt : s * (a * α - b * c) < α * (a * μ - b * c) := by
    have : (s - α) * b * (Ct - c) < 0 := by
      apply mul_neg_of_pos_of_neg (by nlinarith) (by linarith)
    linarith
  have hpos : 0 < s * (a * α - b * c) := by
    have : 0 < s := by linarith
    have : 0 < a * α - b * c := by linarith
    positivity
  have h : (s * (a * α - b * c)) ^ 2 < (α * (a * μ - b * c)) ^ 2 := by nlinarith
  have e1 : (s * (a * α - b * c)) ^ 2 = s ^ 2 * (a * α - b * c) ^ 2 := by ring
  have e2 : (α * (a * μ - b * c)) ^ 2 = α ^ 2 * (a * μ - b * c) ^ 2 := by ring
  rw [e1, e2, hs2] at h
  exact h

lemma g_signs (a b α θ μ N r c1 c : ℝ) (ha : 0 < a) (hb : 0 < b) (hα0 : 0 < α)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hN0 : 0 < N) (hr0 : 0 < r)
    (hfac : -N * (4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2) =
      (b * N * c - a * (α * (1 - θ)) * (μ ^ 2 + θ)) ^ 2 - (2 * a * (α * (1 - θ)) * θ * r) ^ 2)
    (hc1 : b * N * c1 = a * (α * (1 - θ)) * (μ ^ 2 + θ) - 2 * a * (α * (1 - θ)) * θ * r) :
    (c ≤ c1 → 4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2 ≤ 0) ∧
    (c < c1 → 4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2 < 0) ∧
    (c1 < c → b * N * c - a * (α * (1 - θ)) * (μ ^ 2 + θ) < 2 * a * (α * (1 - θ)) * θ * r →
      0 < 4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hY : 0 < 2 * a * (α * (1 - θ)) * θ * r := by positivity
  set Y := 2 * a * (α * (1 - θ)) * θ * r
  set X := b * N * c - a * (α * (1 - θ)) * (μ ^ 2 + θ)
  set Q := 4 * b * μ * θ * c * (a * (α * (1 - θ)) - b * c) -
      (1 - θ) ^ 2 * (α ^ 2 * (1 - θ) + θ) * (a * α - b * c) ^ 2
  have hbN : 0 < b * N := by positivity
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc hc' => ?_⟩
  · have hX : X ≤ -Y := by
      have := mul_le_mul_of_nonneg_left hc hbN.le
      simp only [X]; linarith
    have hsq : Y ^ 2 ≤ X ^ 2 := by nlinarith
    have : 0 ≤ -N * Q := by rw [hfac]; linarith
    nlinarith
  · have hX : X < -Y := by
      have := mul_lt_mul_of_pos_left hc hbN
      simp only [X]; linarith
    have hsq : Y ^ 2 < X ^ 2 := by nlinarith
    have : 0 < -N * Q := by rw [hfac]; linarith
    nlinarith
  · have hX : -Y < X := by
      have := mul_lt_mul_of_pos_left hc hbN
      simp only [X]; linarith
    have hsq : X ^ 2 < Y ^ 2 := by nlinarith
    have : -N * Q < 0 := by rw [hfac]; linarith
    nlinarith

lemma thr (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) :
    0 < Ctil P ∧ Ctil P < cDR1 P ∧ cDR1 P < cDR2 P ∧
    P.b * (1 + P.θ) * cDR2 P ≤ P.a * (P.α * (1 - P.θ)) ∧
    (∀ c, c ≤ cDR1 P → Pf P c ≤ 0) ∧
    (∀ c, c < cDR1 P → Pf P c < 0) ∧
    (∀ c, cDR1 P < c → c ≤ cDR2 P → 0 < Pf P c) ∧
    (∀ c, cDR1 P < c →
      P.a * (P.α * (1 - P.θ)) ^ 2 * (1 - P.α) < P.b * c * P.μ) ∧
    (∀ c, Ctil P < c → P.b * c < P.a * P.α →
      (P.α ^ 2 * (1 - P.θ) + P.θ) * (P.a * P.α - P.b * c) ^ 2 <
        P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := id hP
  obtain ⟨-, hCt0, hCt1, h12⟩ := PPL4_rto_main P.a P.b P.α P.θ ha hb hα hα1 hθ0 hθ1 P.μ rfl
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have h1θ : 0 < 1 - P.θ := by linarith
  have h1α : 0 < 1 - P.α := by linarith
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  obtain ⟨N, hN⟩ : ∃ N, N = P.α ^ 2 * (1 - P.θ) ^ 3 + 4 * P.α * P.θ * (1 - P.θ) +
    P.θ * (1 + P.θ) ^ 2 := ⟨_, rfl⟩
  obtain ⟨r, hr⟩ : ∃ r, r = Real.sqrt (P.α * P.μ * (1 - P.α) * (1 - P.θ)) := ⟨_, rfl⟩
  have hN0 : 0 < N := by rw [hN]; positivity
  have hR2 : 0 < P.α * P.μ * (1 - P.α) * (1 - P.θ) := by positivity
  have hrpos : 0 < r := by rw [hr]; exact Real.sqrt_pos.mpr hR2
  have hrsq : r ^ 2 = P.α * P.μ * (1 - P.α) * (1 - P.θ) := by rw [hr]; exact Real.sq_sqrt hR2.le
  have hr_le : 2 * r ≤ P.α * P.μ + (1 - P.α) * (1 - P.θ) := by
    have : r ≤ (P.α * P.μ + (1 - P.α) * (1 - P.θ)) / 2 := by
      rw [hr, Real.sqrt_le_left]
      · nlinarith [sq_nonneg (P.α * P.μ - (1 - P.α) * (1 - P.θ))]
      · positivity
    linarith
  have hc1 : cDR1 P = P.a * P.α * (1 - P.θ) * (P.μ ^ 2 + P.θ - 2 * P.θ * r) / (P.b * N) := by
    rw [hr, hN]; rfl
  have hc2 : cDR2 P = P.a * P.α * P.μ * (1 - P.θ) / (P.b * (P.μ + P.θ)) := rfl
  have hc1' : P.b * N * cDR1 P = P.a * (P.α * (1 - P.θ)) * (P.μ ^ 2 + P.θ) -
      2 * P.a * (P.α * (1 - P.θ)) * P.θ * r := by
    rw [hc1]; field_simp
  have hfac := fun c => g_fac P.a P.b P.α P.θ P.μ N r c hμ hN hrsq
  have hr2 := g_r2 P.a P.b P.α P.θ P.μ N r ha hb hα hα1 hθ0 hθ1 hμ hN hrpos hrsq
  rw [← hc2] at hr2
  have hsg := fun c => g_signs P.a P.b P.α P.θ P.μ N r (cDR1 P) c ha hb hα0 hθ0 hθ1 hN0 hrpos
    (hfac c) hc1'
  refine ⟨hCt0, hCt1, h12, ?_, fun c hc => (hsg c).1 hc, fun c hc => (hsg c).2.1 hc,
    fun c hc hc' => (hsg c).2.2 hc ?_, fun c hc => ?_, fun c hc hca => ?_⟩
  · rw [hc2]; exact g_c2 P.a P.b P.α P.θ P.μ ha hb hα0 hα1 hθ0 hθ1 hμ
  · have := mul_le_mul_of_nonneg_left hc' (by positivity : (0:ℝ) ≤ P.b * N)
    linarith
  · exact g_F1 P.a P.b P.α P.θ P.μ N r c (cDR1 P) ha hb hα hα1 hθ0 hθ1 hμ hN hr_le hc1' hc
  · have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
    exact g_Ct P.a P.b P.α P.θ P.μ (Real.sqrt (P.α ^ 2 * (1 - P.θ) + P.θ)) (Ctil P) c ha hb hα0
      hα1 hθ0 hθ1 hμ (Real.sqrt_nonneg _) (Real.sq_sqrt hD.le) rfl hc hca

end PPL4


open YieldPostpone.Payment

namespace PPL4

/-- the high-regime optimum value -/
noncomputable def Hv (P : Params) (c : ℝ) : ℝ := (P.a * P.α - P.b * c) ^ 2 / (8 * P.b * P.α ^ 2)

/-- the middle-region quadratic of the supplier's value, in the variable `X = μ w` -/
noncomputable def Q2 (P : Params) (c X : ℝ) : ℝ :=
  (X - c) * (P.a * P.μ - P.b * X) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))

lemma VH_gap (P : Params) (hP : P.Valid) (c w : ℝ) :
    (w - c / P.α) * ((P.a - P.b * w) / 2) = Hv P c - P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  unfold Hv
  field_simp
  ring

lemma VH_le (P : Params) (hP : P.Valid) (c w : ℝ) :
    (w - c / P.α) * ((P.a - P.b * w) / 2) ≤ Hv P c := by
  rw [VH_gap P hP]
  have : 0 ≤ P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by
    have := hP.2.1; positivity
  linarith

lemma VH_lt (P : Params) (hP : P.Valid) (c w : ℝ) (hne : w ≠ (P.a / P.b + c / P.α) / 2) :
    (w - c / P.α) * ((P.a - P.b * w) / 2) < Hv P c := by
  rw [VH_gap P hP]
  have : 0 < P.b / 2 * (w - (P.a / P.b + c / P.α) / 2) ^ 2 := by
    have := hP.2.1
    have : w - (P.a / P.b + c / P.α) / 2 ≠ 0 := sub_ne_zero.mpr hne
    positivity
  linarith

lemma Q2_gap (P : Params) (hP : P.Valid) (c X : ℝ) :
    Q2 P c X = (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) -
      P.b * (X - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  unfold Q2
  field_simp
  ring

lemma Q2_lt_max (P : Params) (hP : P.Valid) (c X : ℝ)
    (hne : X ≠ (P.a * P.μ + P.b * c) / (2 * P.b)) :
    Q2 P c X < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  rw [Q2_gap P hP]
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have : X - (P.a * P.μ + P.b * c) / (2 * P.b) ≠ 0 := sub_ne_zero.mpr hne
  have : 0 < P.b * (X - (P.a * P.μ + P.b * c) / (2 * P.b)) ^ 2 /
      (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by positivity
  linarith

lemma Q2_mono (P : Params) (hP : P.Valid) (c X W : ℝ) (hXW : X ≤ W)
    (hs : P.b * (X + W) ≤ P.a * P.μ + P.b * c) : Q2 P c X ≤ Q2 P c W := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  unfold Q2
  apply div_le_div_of_nonneg_right _ (by positivity)
  have : 0 ≤ (W - X) * (P.a * P.μ + P.b * c - P.b * (X + W)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

lemma Q2_mono_lt (P : Params) (hP : P.Valid) (c X W : ℝ) (hXW : X < W)
    (hs : P.b * (X + W) < P.a * P.μ + P.b * c) : Q2 P c X < Q2 P c W := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have : 0 < 1 - P.θ := by linarith
  have hD : 0 < 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
  unfold Q2
  rw [div_lt_div_iff_of_pos_right hD]
  have : 0 < (W - X) * (P.a * P.μ + P.b * c - P.b * (X + W)) :=
    mul_pos (by linarith) (by linarith)
  nlinarith

/-- classification of the low-regime value `(X - c) qs(X)` -/
lemma VL_cases (P : Params) (hP : P.Valid) (c X : ℝ) (hc : 0 < c) (hX : c < X) :
    (P.b * X < P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ∧ (X - c) * qs P X < Hv P c) ∨
    (P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * X ∧ P.b * X < P.a * P.μ ∧
      (X - c) * qs P X = Q2 P c X) ∨
    (P.a * P.μ ≤ P.b * X ∧ (X - c) * qs P X = 0) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  rcases lt_or_ge (P.b * X) (P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ))) with h3 | h3
  · left
    refine ⟨h3, ?_⟩
    have h1 : P.b * X < P.a * P.μ := by nlinarith
    rw [qs_reg3 P X h1 h3]
    have hreg : P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ) = P.α * (1 - P.θ) * (1 - P.α) := by
      rw [hμ]; ring
    rw [hreg] at h3
    -- AM-GM and the comparison with the high optimum
    have hu : P.b * c < P.a * (P.α * (1 - P.θ)) := by
      have : P.b * c < P.b * X := by nlinarith
      nlinarith [mul_pos (mul_pos ha (mul_pos hα0 h1θ)) hα0]
    have hAM : 4 * P.b * ((X - c) * (P.a * (P.α * (1 - P.θ)) - P.b * X)) ≤
        (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 := by
      nlinarith [sq_nonneg (P.a * (P.α * (1 - P.θ)) + P.b * c - 2 * P.b * X)]
    have hst : (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 < (1 - P.θ) * (P.a * P.α - P.b * c) ^ 2 := by
      have e : (1 - P.θ) * (P.a * P.α - P.b * c) ^ 2 - (P.a * (P.α * (1 - P.θ)) - P.b * c) ^ 2 =
          P.θ * ((P.a * P.α) ^ 2 * (1 - P.θ) - (P.b * c) ^ 2) := by ring
      have hbc0 : 0 < P.b * c := by positivity
      have : (P.b * c) ^ 2 < (P.a * (P.α * (1 - P.θ))) ^ 2 := by nlinarith
      have : (P.a * (P.α * (1 - P.θ))) ^ 2 ≤ (P.a * P.α) ^ 2 * (1 - P.θ) := by
        have e2 : (P.a * (P.α * (1 - P.θ))) ^ 2 = (P.a * P.α) ^ 2 * (1 - P.θ) * (1 - P.θ) := by ring
        rw [e2]
        have : 0 ≤ (P.a * P.α) ^ 2 * (1 - P.θ) := by positivity
        nlinarith
      have : 0 < P.θ * ((P.a * P.α) ^ 2 * (1 - P.θ) - (P.b * c) ^ 2) := by
        apply mul_pos hθ0; linarith
      linarith
    unfold Hv
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hk : 0 < 2 * P.α ^ 2 := by positivity
    have h5 : 4 * P.b * ((X - c) * (P.a * (P.α * (1 - P.θ)) - P.b * X)) <
        (1 - P.θ) * (P.a * P.α - P.b * c) ^ 2 := by linarith
    have h6 := mul_lt_mul_of_pos_left h5 hk
    nlinarith
  · rcases lt_or_ge (P.b * X) (P.a * P.μ) with h1 | h1
    · right; left
      refine ⟨h3, h1, ?_⟩
      rw [qs_reg2 P X h1 h3]
      unfold Q2
      ring
    · right; right
      exact ⟨h1, by rw [qs_reg1 P X h1]; ring⟩

end PPL4


open YieldPostpone.Payment

namespace PPL4

lemma Q2W_sub (P : Params) (hP : P.Valid) (c : ℝ) :
    Q2 P c (P.μ * (c / (P.α * (1 - P.θ)))) - Hv P c =
      Pf P c / (8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  unfold Q2 Hv Pf
  rw [div_sub_div _ _ (by positivity) (by positivity), div_eq_div_iff (by positivity) (by positivity)]
  field_simp
  rw [hμ]
  ring

lemma Hv_lt_g2 (P : Params) (hP : P.Valid) (c : ℝ)
    (h : (P.α ^ 2 * (1 - P.θ) + P.θ) * (P.a * P.α - P.b * c) ^ 2 <
        P.α ^ 2 * (P.a * P.μ - P.b * c) ^ 2) :
    Hv P c < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP
  have h1θ : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  unfold Hv
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have := mul_lt_mul_of_pos_left h (by positivity : (0:ℝ) < 8 * P.b)
  nlinarith

/-- low-regime values when `c ≤ c^DR_2` (so that `μ w₀` lies left of the middle peak) -/
lemma low_cases (P : Params) (hP : P.Valid) (c : ℝ) (hc0 : 0 < c)
    (hc2' : P.b * (P.μ + P.θ) * c ≤ P.a * (P.α * (1 - P.θ)) * P.μ)
    (w : ℝ) (hw : wAdm P c .DR w) (hl : P.α * (1 - P.θ) * w ≤ c) :
    (P.μ * w - c) * qs P (P.μ * w) < Hv P c ∨
    ((P.μ * w - c) * qs P (P.μ * w) ≤ Q2 P c (P.μ * (c / (P.α * (1 - P.θ)))) ∧
      (w < c / (P.α * (1 - P.θ)) →
        (P.μ * w - c) * qs P (P.μ * w) < Q2 P c (P.μ * (c / (P.α * (1 - P.θ)))))) ∨
    (P.μ * w - c) * qs P (P.μ * w) = 0 := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hu : 0 < P.α * (1 - P.θ) := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  obtain ⟨hwμ, hw0⟩ := wpos P hP c w hc0 hw
  have hX : c < P.μ * w := by rw [hμ]; linarith
  have hwW : w ≤ c / (P.α * (1 - P.θ)) := by rw [le_div_iff₀ hu]; linarith
  have hsW : P.b * (2 * (P.μ * (c / (P.α * (1 - P.θ))))) ≤ P.a * P.μ + P.b * c := by
    have e : P.b * (2 * (P.μ * (c / (P.α * (1 - P.θ))))) * (P.α * (1 - P.θ)) =
        2 * P.b * P.μ * c := by field_simp
    rw [← mul_le_mul_iff_of_pos_right hu, e]
    rw [hμ] at hc2' ⊢; nlinarith
  rcases VL_cases P hP c (P.μ * w) hc0 hX with ⟨-, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
  · exact Or.inl h
  · right; left
    rw [h]
    have hXW : P.μ * w ≤ P.μ * (c / (P.α * (1 - P.θ))) := mul_le_mul_of_nonneg_left hwW hμ0.le
    refine ⟨Q2_mono P hP c _ _ hXW (by nlinarith), fun hlt => ?_⟩
    have hXW' : P.μ * w < P.μ * (c / (P.α * (1 - P.θ))) := mul_lt_mul_of_pos_left hlt hμ0
    exact Q2_mono_lt P hP c _ _ hXW' (by nlinarith)
  · right; right; exact h

/-- Case `c ≤ c^DR_1`: the inflated-production price `w₃` is optimal. -/
lemma supA (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) (c : ℝ) (hc0 : 0 < c)
    (hc : c ≤ cDR1 P) :
    wAdm P c .DR ((P.a / P.b + c / P.α) / 2) ∧
    c < P.α * (1 - P.θ) * ((P.a / P.b + c / P.α) / 2) ∧
    P.b * c < P.a * P.α ∧
    Vd P c ((P.a / P.b + c / P.α) / 2) = Hv P c ∧
    (∀ w, wAdm P c .DR w → Vd P c w ≤ Hv P c) ∧
    (c < cDR1 P → ∀ w, wAdm P c .DR w → w ≠ (P.a / P.b + c / P.α) / 2 → Vd P c w < Hv P c) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hCt0, hCt1, h12, hc2b, hPle, hPlt, -, -, -⟩ := thr P hP hα
  have h1θ : 0 < 1 - P.θ := by linarith
  have hu : 0 < P.α * (1 - P.θ) := by positivity
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  have hc2 : c < cDR2 P := lt_of_le_of_lt hc h12
  have hcu : P.b * (1 + P.θ) * c < P.a * (P.α * (1 - P.θ)) := by
    have := mul_lt_mul_of_pos_left hc2 (by positivity : (0:ℝ) < P.b * (1 + P.θ))
    linarith
  have hca : P.b * c < P.a * P.α := by
    nlinarith [mul_pos (mul_pos hb hc0) hθ0, mul_pos (mul_pos ha hα0) hθ0]
  have hc2' : P.b * (P.μ + P.θ) * c ≤ P.a * (P.α * (1 - P.θ)) * P.μ := by
    have e : cDR2 P * (P.b * (P.μ + P.θ)) = P.a * P.α * P.μ * (1 - P.θ) := by
      unfold cDR2; field_simp
    have := mul_le_mul_of_nonneg_left hc2.le (by positivity : (0:ℝ) ≤ P.b * (P.μ + P.θ))
    nlinarith
  set w3 := (P.a / P.b + c / P.α) / 2 with hw3
  have e1 : P.α * (1 - P.θ) * w3 - c = (P.a * (P.α * (1 - P.θ)) - P.b * (1 + P.θ) * c) / (2 * P.b) := by
    rw [hw3]; field_simp; ring
  have hhigh : c < P.α * (1 - P.θ) * w3 := by
    have : 0 < (P.a * (P.α * (1 - P.θ)) - P.b * (1 + P.θ) * c) / (2 * P.b) :=
      div_pos (by linarith) (by positivity)
    linarith
  have e2 : P.a / P.b - w3 = (P.a * P.α - P.b * c) / (2 * P.b * P.α) := by
    rw [hw3]; field_simp; ring
  have hw3a : w3 < P.a / P.b := by
    have : 0 < (P.a * P.α - P.b * c) / (2 * P.b * P.α) := div_pos (by linarith) (by positivity)
    linarith
  have hw3pos : 0 < w3 := by rw [hw3]; positivity
  have hadm : wAdm P c .DR w3 := by
    rw [wAdm_DR]
    refine ⟨?_, hw3a⟩
    rw [div_lt_iff₀ hμ0]
    have : P.α * (1 - P.θ) * w3 ≤ w3 * P.μ := by rw [hμ]; nlinarith
    linarith
  have hV3 : Vd P c w3 = Hv P c := by
    unfold Vd
    rw [if_neg (not_le.mpr hhigh), VH_gap P hP, hw3]
    ring
  have hQW := Q2W_sub P hP c
  have hden : 0 < 8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
  have hHv : 0 < Hv P c := by
    unfold Hv
    have : 0 < P.a * P.α - P.b * c := by linarith
    positivity
  have hQle : Q2 P c (P.μ * (c / (P.α * (1 - P.θ)))) ≤ Hv P c := by
    have : Pf P c / (8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (hPle c hc) hden.le
    linarith
  refine ⟨hadm, hhigh, hca, hV3, fun w hw => ?_, fun hlt w hw hne => ?_⟩
  · unfold Vd
    split_ifs with hl
    · rcases low_cases P hP c hc0 hc2' w hw hl with h | ⟨h, -⟩ | h
      · exact h.le
      · linarith
      · rw [h]; exact hHv.le
    · exact VH_le P hP c w
  · have hQlt : Q2 P c (P.μ * (c / (P.α * (1 - P.θ)))) < Hv P c := by
      have : Pf P c / (8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) < 0 :=
        div_neg_of_neg_of_pos (hPlt c hlt) hden
      linarith
    unfold Vd
    split_ifs with hl
    · rcases low_cases P hP c hc0 hc2' w hw hl with h | ⟨h, -⟩ | h
      · exact h
      · linarith
      · rw [h]; exact hHv
    · exact VH_lt P hP c w hne

end PPL4


open YieldPostpone.Payment

namespace PPL4

/-- Case `c^DR_1 < c ≤ c^DR_2`: the boundary price `w₀ = c/(α(1-θ))` is optimal. -/
lemma supB (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) (c : ℝ) (hc0 : 0 < c)
    (hc1 : cDR1 P < c) (hc : c ≤ cDR2 P) :
    wAdm P c .DR (c / (P.α * (1 - P.θ))) ∧
    P.α * (1 - P.θ) * (c / (P.α * (1 - P.θ))) ≤ c ∧
    P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (P.μ * (c / (P.α * (1 - P.θ)))) ∧
    P.b * (P.μ * (c / (P.α * (1 - P.θ)))) < P.a * P.μ ∧
    (∀ w, wAdm P c .DR w → w ≠ c / (P.α * (1 - P.θ)) →
      Vd P c w < Vd P c (c / (P.α * (1 - P.θ)))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hCt0, hCt1, h12, hc2b, -, -, hPpos, hF1, -⟩ := thr P hP hα
  have h1θ : 0 < 1 - P.θ := by linarith
  have hu : 0 < P.α * (1 - P.θ) := by positivity
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  have hcu : P.b * (1 + P.θ) * c ≤ P.a * (P.α * (1 - P.θ)) := by
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ P.b * (1 + P.θ))
    linarith
  have hcu' : P.b * c < P.a * (P.α * (1 - P.θ)) := by
    nlinarith [mul_pos (mul_pos hb hc0) hθ0]
  have hc2' : P.b * (P.μ + P.θ) * c ≤ P.a * (P.α * (1 - P.θ)) * P.μ := by
    have e : cDR2 P * (P.b * (P.μ + P.θ)) = P.a * P.α * P.μ * (1 - P.θ) := by
      unfold cDR2; field_simp
    have := mul_le_mul_of_nonneg_left hc (by positivity : (0:ℝ) ≤ P.b * (P.μ + P.θ))
    nlinarith
  set w0 := c / (P.α * (1 - P.θ)) with hw0
  have hw0u : P.α * (1 - P.θ) * w0 = c := by rw [hw0]; field_simp
  have hX0 : P.μ * w0 * (P.α * (1 - P.θ)) = P.μ * c := by rw [hw0]; field_simp
  have hw0pos : 0 < w0 := by rw [hw0]; positivity
  have hadm : wAdm P c .DR w0 := by
    rw [wAdm_DR]
    constructor
    · rw [div_lt_iff₀ hμ0]
      have : P.α * (1 - P.θ) * w0 < w0 * P.μ := by rw [hμ]; nlinarith
      linarith
    · rw [lt_div_iff₀ hb]
      have : P.b * w0 * (P.α * (1 - P.θ)) < P.a * (P.α * (1 - P.θ)) := by nlinarith
      nlinarith
  have hR2lo : P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (P.μ * w0) := by
    have hreg : P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ) = P.α * (1 - P.θ) * (1 - P.α) := by
      rw [hμ]; ring
    rw [hreg]
    have h := hF1 c hc1
    have : P.a * (P.α * (1 - P.θ) * (1 - P.α)) * (P.α * (1 - P.θ)) ≤
        P.b * (P.μ * w0) * (P.α * (1 - P.θ)) := by
      have e : P.b * (P.μ * w0) * (P.α * (1 - P.θ)) = P.b * c * P.μ := by
        rw [mul_assoc, hX0]; ring
      rw [e]; nlinarith
    exact le_of_mul_le_mul_right this hu
  have hR2hi : P.b * (P.μ * w0) < P.a * P.μ := by
    have : P.b * (P.μ * w0) * (P.α * (1 - P.θ)) < P.a * P.μ * (P.α * (1 - P.θ)) := by
      have e : P.b * (P.μ * w0) * (P.α * (1 - P.θ)) = P.b * c * P.μ := by
        rw [mul_assoc, hX0]; ring
      rw [e]; nlinarith
    exact lt_of_mul_lt_mul_right this hu.le
  have hV0 : Vd P c w0 = Q2 P c (P.μ * w0) := by
    unfold Vd
    rw [if_pos hw0u.le, qs_reg2 P _ hR2hi hR2lo]
    unfold Q2; ring
  have hQW := Q2W_sub P hP c
  rw [← hw0] at hQW
  have hden : 0 < 8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) := by positivity
  have hQgt : Hv P c < Q2 P c (P.μ * w0) := by
    have : 0 < Pf P c / (8 * P.b * (P.α * (1 - P.θ)) ^ 2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) :=
      div_pos (hPpos c hc1 hc) hden
    linarith
  have hQpos : 0 < Q2 P c (P.μ * w0) := by
    unfold Q2
    apply div_pos _ (by positivity)
    apply mul_pos
    · have : c < P.μ * w0 := by
        have : P.α * (1 - P.θ) * w0 < P.μ * w0 := by rw [hμ]; nlinarith
        linarith
      linarith
    · linarith
  refine ⟨hadm, hw0u.le, hR2lo, hR2hi, fun w hw hne => ?_⟩
  rw [hV0]
  unfold Vd
  split_ifs with hl
  · have hlt : w < w0 := by
      have : w ≤ w0 := by rw [hw0, le_div_iff₀ hu]; linarith
      exact lt_of_le_of_ne this hne
    rcases low_cases P hP c hc0 hc2' w hw hl with h | ⟨-, h⟩ | h
    · linarith
    · exact h hlt
    · rw [h]; exact hQpos
  · have := VH_le P hP c w
    linarith

/-- Case `c > c^DR_2`: the interior price `w₂ = (aμ + bc)/(2bμ)` is optimal. -/
lemma supC (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) (c : ℝ) (hc0 : 0 < c)
    (hcμ : P.b * c < P.a * P.μ) (hc : cDR2 P < c) :
    wAdm P c .DR ((P.a * P.μ + P.b * c) / (2 * P.b * P.μ)) ∧
    P.α * (1 - P.θ) * ((P.a * P.μ + P.b * c) / (2 * P.b * P.μ)) ≤ c ∧
    P.μ * ((P.a * P.μ + P.b * c) / (2 * P.b * P.μ)) = (P.a * P.μ + P.b * c) / (2 * P.b) ∧
    P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * ((P.a * P.μ + P.b * c) / (2 * P.b)) ∧
    P.b * ((P.a * P.μ + P.b * c) / (2 * P.b)) < P.a * P.μ ∧
    (∀ w, wAdm P c .DR w → w ≠ (P.a * P.μ + P.b * c) / (2 * P.b * P.μ) →
      Vd P c w < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ))) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨hCt0, hCt1, h12, hc2b, -, -, -, -, hCtc⟩ := thr P hP hα
  have h1θ : 0 < 1 - P.θ := by linarith
  have hu : 0 < P.α * (1 - P.θ) := by positivity
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  have hc2' : P.a * (P.α * (1 - P.θ)) * P.μ < P.b * (P.μ + P.θ) * c := by
    have e : cDR2 P * (P.b * (P.μ + P.θ)) = P.a * P.α * P.μ * (1 - P.θ) := by
      unfold cDR2; field_simp
    have := mul_lt_mul_of_pos_left hc (by positivity : (0:ℝ) < P.b * (P.μ + P.θ))
    nlinarith
  set w2 := (P.a * P.μ + P.b * c) / (2 * P.b * P.μ) with hw2
  have hX2 : P.μ * w2 = (P.a * P.μ + P.b * c) / (2 * P.b) := by rw [hw2]; field_simp
  have hbX2 : P.b * ((P.a * P.μ + P.b * c) / (2 * P.b)) = (P.a * P.μ + P.b * c) / 2 := by
    field_simp
  have hlow2 : P.α * (1 - P.θ) * w2 ≤ c := by
    rw [hw2, ← mul_div_assoc, div_le_iff₀ (by positivity)]
    rw [hμ] at hc2' ⊢; nlinarith
  have hadm : wAdm P c .DR w2 := by
    rw [wAdm_DR]
    constructor
    · rw [div_lt_iff₀ hμ0, mul_comm, hX2, lt_div_iff₀ (by positivity)]; nlinarith
    · rw [hw2, div_lt_div_iff₀ (by positivity) hb]; nlinarith
  have hR2lo : P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * ((P.a * P.μ + P.b * c) / (2 * P.b)) := by
    rw [hbX2, hμ]
    have : 0 < P.α * (1 - P.θ) * (2 * P.α - 1) + P.θ := by
      have : 0 < 2 * P.α - 1 := by linarith
      positivity
    nlinarith [mul_pos ha this, mul_pos hb hc0]
  have hR2hi : P.b * ((P.a * P.μ + P.b * c) / (2 * P.b)) < P.a * P.μ := by rw [hbX2]; linarith
  have hgpos : 0 < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    have : 0 < P.a * P.μ - P.b * c := by linarith
    positivity
  have hHvg : P.b * c < P.a * P.α →
      Hv P c < (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
    intro hca
    exact Hv_lt_g2 P hP c (hCtc c (by linarith) hca)
  refine ⟨hadm, hlow2, hX2, hR2lo, hR2hi, fun w hw hne => ?_⟩
  obtain ⟨hwμ, hw0⟩ := wpos P hP c w hc0 hw
  have hwa : w < P.a / P.b := ((wAdm_DR P c w).mp hw).2
  unfold Vd
  split_ifs with hl
  · have hX : c < P.μ * w := by rw [hμ]; linarith
    rcases VL_cases P hP c (P.μ * w) hc0 hX with ⟨h3, h⟩ | ⟨-, -, h⟩ | ⟨-, h⟩
    · have hreg : P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ) = P.α * (1 - P.θ) * (1 - P.α) := by
        rw [hμ]; ring
      rw [hreg] at h3
      have hca : P.b * c < P.a * P.α := by
        have h4 : P.b * c < P.b * (P.μ * w) := mul_lt_mul_of_pos_left hX hb
        have h5 : P.a * (P.α * (1 - P.θ) * (1 - P.α)) < P.a * P.α := by
          have h6 : (1 - P.θ) * (1 - P.α) < 1 :=
            mul_lt_one_of_nonneg_of_lt_one_left h1θ.le (by linarith) (by linarith)
          have h7 : P.α * (1 - P.θ) * (1 - P.α) < P.α := by
            rw [mul_assoc]; exact mul_lt_of_lt_one_right hα0 h6
          exact mul_lt_mul_of_pos_left h7 ha
        linarith
      exact lt_trans h (hHvg hca)
    · rw [h]
      apply Q2_lt_max P hP
      intro heq
      apply hne
      rw [← hX2] at heq
      exact mul_left_cancel₀ hμ0.ne' heq
    · rw [h]; exact hgpos
  · rcases lt_or_ge (P.b * c) (P.a * P.α) with hca | hca
    · exact lt_of_le_of_lt (VH_le P hP c w) (hHvg hca)
    · have h1 : w - c / P.α < 0 := by
        have : P.a / P.b ≤ c / P.α := by
          rw [div_le_div_iff₀ hb hα0]; linarith
        linarith
      have h2 : 0 < (P.a - P.b * w) / 2 := by
        rw [lt_div_iff₀ hb] at hwa; linarith
      have : (w - c / P.α) * ((P.a - P.b * w) / 2) < 0 := mul_neg_of_neg_of_pos h1 h2
      linarith

end PPL4


open YieldPostpone.Payment

namespace PPL4

lemma CS_eqR (P : Params) (c : ℝ) (σ : Profile) :
    CS P c .DR σ =
      P.θ * surplus P (σ.pr σ.w (σ.q σ.w) (min (σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)))
        (min (σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) +
      (1 - P.θ) * surplus P (σ.pr σ.w (σ.q σ.w) (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)))
        (min (P.α * σ.Q σ.w (σ.q σ.w)) (σ.q σ.w)) := by
  simp only [CS, E, delivered, Scenario.responsive, if_true, one_mul]

lemma VdC (P : Params) (hP : P.Valid) (c w : ℝ) (hl : P.α * (1 - P.θ) * w ≤ c)
    (hX : P.μ * w = (P.a * P.μ + P.b * c) / (2 * P.b))
    (h1 : P.b * (P.μ * w) < P.a * P.μ)
    (h2 : P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (P.μ * w)) :
    Vd P c w = (P.a * P.μ - P.b * c) ^ 2 / (8 * P.b * (P.α ^ 2 * (1 - P.θ) + P.θ)) := by
  unfold Vd
  rw [if_pos hl, qs_reg2 P _ h1 h2]
  have := Q2_gap P hP c (P.μ * w)
  unfold Q2 at this
  rw [mul_div_assoc', this, hX]
  ring

/-- equilibrium outcome when the equilibrium wholesale price is in the low regime and
`μ w` lies in the middle region -/
lemma outcome_low (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (hl : P.α * (1 - P.θ) * σ.w ≤ c)
    (h1 : P.b * (P.μ * σ.w) < P.a * P.μ)
    (h2 : P.a * (P.μ - (P.α ^ 2 * (1 - P.θ) + P.θ)) ≤ P.b * (P.μ * σ.w)) :
    piR P c .DR σ = (P.α ^ 2 * (1 - P.θ) + P.θ) *
        ((P.a * P.μ - P.b * (P.μ * σ.w)) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ^ 2 / P.b ∧
    piS P c .DR σ = (P.μ * σ.w - c) *
        ((P.a * P.μ - P.b * (P.μ * σ.w)) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ∧
    CS P c .DR σ = (P.α ^ 2 * (1 - P.θ) + P.θ) *
        ((P.a * P.μ - P.b * (P.μ * σ.w)) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ))) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have h1θ : 0 < 1 - P.θ := by linarith
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  obtain ⟨-, hpr, -, hw, -⟩ := (isSPE_DR P c σ).mp hσ
  set q := (P.a * P.μ - P.b * (P.μ * σ.w)) / (2 * (P.α ^ 2 * (1 - P.θ) + P.θ)) with hqdef
  have hqs : qs P (P.μ * σ.w) = q := qs_reg2 P _ h1 h2
  have hq : σ.q σ.w = q := by
    rw [qR_spe P hP c hc σ hσ σ.w hw]; unfold qR; rw [if_pos hl, hqs]
  have hq0 : 0 < q := by rw [hqdef]; apply div_pos (by linarith) (by positivity)
  have hQ : σ.Q σ.w q = q := by
    rw [QcharR P hP c hc σ hσ σ.w q hw hq0.le, if_pos hl]
  have hqa : q ≤ P.a / 2 := by
    rw [hqdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hαq : P.α * q ≤ q := by nlinarith
  have hαqa : P.α * q ≤ P.a / 2 := le_trans hαq hqa
  have hbX : P.b * (P.μ * σ.w) = P.a * P.μ - 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * q := by
    rw [hqdef]; field_simp; ring
  refine ⟨?_, ?_, ?_⟩
  · unfold piR
    rw [hq, RP_lowR P hP σ hpr σ.w q _ hq0.le hQ]
    unfold Pi
    rw [Rv_le P q hqa, Rv_le P _ hαqa]
    have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
    have e : P.μ * σ.w * q = (P.a * P.μ - 2 * (P.α ^ 2 * (1 - P.θ) + P.θ) * q) * q / P.b := by
      rw [← hbX]; field_simp
    rw [e, hμ]
    field_simp
    ring
  · unfold piS
    rw [SV_R P hP c hc σ σ.w hw (fun q' hq' => QcharR P hP c hc σ hσ σ.w q' hw hq')
      (qR_spe P hP c hc σ hσ σ.w hw)]
    unfold Vd
    rw [if_pos hl, hqs]
  · rw [CS_eqR, hq, hQ, min_self, min_eq_left hαq,
      surplus_opt P hP q hq0 _ (hpr _ _ _ hq0.le).1 (hpr _ _ _ hq0.le).2,
      surplus_opt P hP (P.α * q) (by positivity) _ (hpr _ _ _ (by positivity)).1
        (hpr _ _ _ (by positivity)).2]
    unfold Sv
    rw [if_pos hqa, if_pos hαqa]
    field_simp
    ring

/-- equilibrium outcome when the equilibrium wholesale price is in the high regime -/
lemma outcome_high (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (hh : c < P.α * (1 - P.θ) * σ.w) :
    piR P c .DR σ = ((P.a - P.b * σ.w) / 2) ^ 2 / P.b ∧
    piS P c .DR σ = (σ.w - c / P.α) * ((P.a - P.b * σ.w) / 2) ∧
    CS P c .DR σ = ((P.a - P.b * σ.w) / 2) ^ 2 / (2 * P.b) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  obtain ⟨-, hpr, -, hw, -⟩ := (isSPE_DR P c σ).mp hσ
  obtain ⟨-, hw0⟩ := wpos P hP c σ.w hc hw
  have hwa : P.b * σ.w < P.a := by
    have := ((wAdm_DR P c σ.w).mp hw).2
    rwa [lt_div_iff₀ hb, mul_comm] at this
  set q := (P.a - P.b * σ.w) / 2 with hqdef
  have hq : σ.q σ.w = q := by
    rw [qR_spe P hP c hc σ hσ σ.w hw]; unfold qR; rw [if_neg (not_le.mpr hh)]
  have hq0 : 0 < q := by rw [hqdef]; linarith
  have hQ : σ.Q σ.w q = q / P.α := by
    rw [QcharR P hP c hc σ hσ σ.w q hw hq0.le, if_neg (not_le.mpr hh)]
  have hqa : q ≤ P.a / 2 := by
    rw [hqdef]; have : 0 < P.b * σ.w := by positivity
    linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold piR
    rw [hq, RP_highR P hP σ hpr σ.w q _ hq0.le hQ, Rv_le P q hqa, hqdef]
    field_simp
    ring
  · unfold piS
    rw [SV_R P hP c hc σ σ.w hw (fun q' hq' => QcharR P hP c hc σ hσ σ.w q' hw hq')
      (qR_spe P hP c hc σ hσ σ.w hw)]
    unfold Vd
    rw [if_neg (not_le.mpr hh)]
  · have hqα : q ≤ q / P.α := by rw [le_div_iff₀ hα0]; nlinarith
    have hαqα : P.α * (q / P.α) = q := by field_simp
    rw [CS_eqR, hq, hQ, min_eq_right hqα, hαqα, min_self,
      surplus_opt P hP q hq0 _ (hpr _ _ _ hq0.le).1 (hpr _ _ _ hq0.le).2]
    unfold Sv
    rw [if_pos hqa]
    ring

end PPL4


open YieldPostpone.Payment

namespace PPL4

lemma SV_spe (P : Params) (hP : P.Valid) (c : ℝ) (hc : 0 < c) (σ : Profile)
    (hσ : IsSPE P c .DR σ) (w : ℝ) (hw : wAdm P c .DR w) :
    supplierValue P c .DR σ w = Vd P c w :=
  SV_R P hP c hc σ w hw (fun q hq => QcharR P hP c hc σ hσ w q hw hq) (qR_spe P hP c hc σ hσ w hw)

/-- the explicit equilibrium profile -/
noncomputable def σE (P : Params) (c ws : ℝ) : Profile :=
  ⟨ws, fun w q => if P.α * (1 - P.θ) * w ≤ c then q else q / P.α, fun w => qR P c w,
    fun _ => 0, fun _ _ x => prf P x⟩

lemma σE_spe (P : Params) (hP : P.Valid) (c ws : ℝ) (hc : 0 < c) (hws : wAdm P c .DR ws)
    (hmax : ∀ w, wAdm P c .DR w → Vd P c w ≤ Vd P c ws) :
    IsSPE P c .DR (σE P c ws) := by
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hpr : ∀ w q x : ℝ, 0 ≤ x →
      pAdm P ((σE P c ws).pr w q x) ∧
        ∀ p', pAdm P p' → salesRev P p' x ≤ salesRev P ((σE P c ws).pr w q x) x :=
    fun w q x hx => prf_opt P hP x hx
  have hQ : ∀ w q, (σE P c ws).Q w q = if P.α * (1 - P.θ) * w ≤ c then q else q / P.α :=
    fun _ _ => rfl
  refine (isSPE_DR P c _).mpr ⟨?_, hpr, ?_, hws, ?_⟩
  · intro w q hw hq
    have hwμ := (wpos P hP c w hc hw).1
    rw [hQ]
    split_ifs with hl
    · refine ⟨hq, fun Q' hQ' => ?_, fun _ => rfl⟩
      rw [sp_eqR, sp_eqR]
      exact prod_low P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hl hq hQ'
    · push Not at hl
      refine ⟨by positivity, fun Q' hQ' => ?_, fun h => ?_⟩
      · rw [sp_eqR, sp_eqR]
        exact (prod_high P.α P.θ c w q Q' hα0 hα1 hθ0 hθ1 hc hwμ hl hq hQ').1
      · have h1 := h (q / P.α) (by positivity)
        rw [sp_eqR, sp_eqR] at h1
        obtain ⟨h2, h3⟩ := prod_high P.α P.θ c w q q hα0 hα1 hθ0 hθ1 hc hwμ hl hq hq
        exact (h3 (le_antisymm h2 h1)).symm
  · intro w hw
    refine ⟨qR_nonneg P hP c w hc hw, trivial, fun q' p' hq' _ => ?_⟩
    by_cases he : q' = qR P c w
    · show retailerProfit P .DR (σE P c ws) w q' p' ≤
        retailerProfit P .DR (σE P c ws) w (qR P c w) ((σE P c ws).p w)
      rw [he, rp_eqR, rp_eqR]
    · exact (retR P hP c hc _ hpr w hw (fun q _ => hQ w q) q' p' _ hq' he).le
  · intro w' hw'
    show supplierValue P c .DR (σE P c ws) w' ≤ supplierValue P c .DR (σE P c ws) ws
    rw [SV_R P hP c hc _ w' hw' (fun q _ => hQ w' q) rfl,
      SV_R P hP c hc _ ws hws (fun q _ => hQ ws q) rfl]
    exact hmax w' hw'

end PPL4

open PPL4

theorem solution (P : Params) (hP : P.Valid) (hα : (9 : ℝ) / 16 ≤ P.α) :
    ∀ c, costAdm P c →
      (∃ σ : Profile, IsSPE P c .DR σ) ∧
      (∀ σ : Profile, IsSPE P c .DR σ →
        (c < cDR1 P → outcome P c .DR σ = DR1 P c) ∧
        (cDR1 P < c ∧ c < cDR2 P → outcome P c .DR σ = DR2 P c) ∧
        (cDR2 P < c → outcome P c .DR σ = DR3 P c)) := by
  intro c hc
  obtain ⟨hc0, hcμ'⟩ := hc
  have hP' := hP
  obtain ⟨ha, hb, hα0, hα1, hθ0, hθ1⟩ := hP'
  have hcμ : P.b * c < P.a * P.μ := by rw [lt_div_iff₀ hb] at hcμ'; linarith
  have h1θ : 0 < 1 - P.θ := by linarith
  have hu : 0 < P.α * (1 - P.θ) := by positivity
  have hD : 0 < P.α ^ 2 * (1 - P.θ) + P.θ := by positivity
  have hμ : P.μ = P.α * (1 - P.θ) + P.θ := rfl
  have hμ0 : 0 < P.μ := by rw [hμ]; positivity
  constructor
  · -- existence
    by_cases hA : c ≤ cDR1 P
    · obtain ⟨hadm, -, -, hV, hle, -⟩ := supA P hP hα c hc0 hA
      exact ⟨_, σE_spe P hP c _ hc0 hadm (fun w hw => (hle w hw).trans_eq hV.symm)⟩
    · push Not at hA
      by_cases hB : c ≤ cDR2 P
      · obtain ⟨hadm, -, -, -, hlt⟩ := supB P hP hα c hc0 hA hB
        refine ⟨_, σE_spe P hP c _ hc0 hadm (fun w hw => ?_)⟩
        by_cases he : w = c / (P.α * (1 - P.θ))
        · rw [he]
        · exact (hlt w hw he).le
      · push Not at hB
        obtain ⟨hadm, hl, hX, h2, h1, hlt⟩ := supC P hP hα c hc0 hcμ hB
        have hV := VdC P hP c _ hl hX (by rw [hX]; exact h1) (by rw [hX]; exact h2)
        refine ⟨_, σE_spe P hP c _ hc0 hadm (fun w hw => ?_)⟩
        by_cases he : w = (P.a * P.μ + P.b * c) / (2 * P.b * P.μ)
        · rw [he]
        · rw [hV]; exact (hlt w hw he).le
  · intro σ hσ
    obtain ⟨-, -, -, hw, hopt⟩ := (isSPE_DR P c σ).mp hσ
    have hopt' : ∀ w, wAdm P c .DR w → Vd P c w ≤ Vd P c σ.w := by
      intro w hw'
      have := hopt w hw'
      rwa [SV_spe P hP c hc0 σ hσ w hw', SV_spe P hP c hc0 σ hσ σ.w hw] at this
    refine ⟨fun hA => ?_, fun ⟨hB1, hB2⟩ => ?_, fun hC => ?_⟩
    · obtain ⟨hadm, hhigh, hca, hV, -, hlt⟩ := supA P hP hα c hc0 hA.le
      have hws : σ.w = (P.a / P.b + c / P.α) / 2 := by
        by_contra hne
        have h1 := hlt hA σ.w hw hne
        have h2 := hopt' _ hadm
        linarith
      rw [← hws] at hhigh
      obtain ⟨e1, e2, e3⟩ := outcome_high P hP c hc0 σ hσ hhigh
      unfold outcome DR1
      rw [e1, e2, e3, hws]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring
    · obtain ⟨hadm, hl, h2, h1, hlt⟩ := supB P hP hα c hc0 hB1 hB2.le
      have hws : σ.w = c / (P.α * (1 - P.θ)) := by
        by_contra hne
        have h1 := hlt σ.w hw hne
        have h2 := hopt' _ hadm
        linarith
      rw [← hws] at hl h1 h2
      obtain ⟨e1, e2, e3⟩ := outcome_low P hP c hc0 σ hσ hl h1 h2
      unfold outcome DR2
      rw [e1, e2, e3, hws, hμ]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring
    · obtain ⟨hadm, hl, hX, h2, h1, hlt⟩ := supC P hP hα c hc0 hcμ hC
      have hV := VdC P hP c _ hl hX (by rw [hX]; exact h1) (by rw [hX]; exact h2)
      have hws : σ.w = (P.a * P.μ + P.b * c) / (2 * P.b * P.μ) := by
        by_contra hne
        have h1 := hlt σ.w hw hne
        have h2 := hopt' _ hadm
        linarith
      rw [← hws] at hl hX
      rw [← hX] at h1 h2
      obtain ⟨e1, e2, e3⟩ := outcome_low P hP c hc0 σ hσ hl h1 h2
      unfold outcome DR3 OR2
      rw [e1, e2, e3, hX]
      refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only <;> field_simp <;> ring

