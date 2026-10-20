-- Prove2me | solution 1 for SharingPlatform.WageSchemes.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:51:09.684441+00:00
-- url     : https://prove2.me/submissions/aa5d4930-8ca1-4caf-aaa6-4bab66a65996

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

open SharingPlatform.WageSchemes

/-- Upper bound for any deviation `(p, w)` against a rival `(p0, w0)`, given a reference point
`(ps, ws, qs)` on the line `d = s = qs` satisfying the first-order condition. -/
private lemma dev_upper (P : Params) (hb : 0 < P.b) (hc : 0 < P.c) (hl : 0 < P.l)
    (hm : 0 < P.m) (p0 w0 ps ws qs p w : ℝ)
    (h1 : (P.b + P.c) * ps = P.a + P.b * p0 - qs)
    (h2 : (P.l + P.m) * ws = qs + P.k + P.l * w0)
    (h3 : ps - ws = (1 / (P.b + P.c) + 1 / (P.l + P.m)) * qs) :
    profit P p w p0 w0 ≤ (1 / (P.b + P.c) + 1 / (P.l + P.m)) * qs ^ 2 := by
  have hbc : 0 < P.b + P.c := by linarith
  have hlm : 0 < P.l + P.m := by linarith
  set β := 1 / (P.b + P.c) + 1 / (P.l + P.m) with hβ
  have hβpos : 0 < β := by positivity
  unfold profit volume
  set d := demand P p p0 with hd
  set s := supply P w w0 with hs
  by_cases hv : min d s ≤ 0
  · rw [max_eq_left hv, mul_zero]; positivity
  · push_neg at hv
    rw [max_eq_right hv.le]
    set q := min d s with hq
    have hdq : q ≤ d := min_le_left _ _
    have hsq : q ≤ s := min_le_right _ _
    have hd' : d = P.a - P.b * (p - p0) - P.c * p := rfl
    have hs' : s = -P.k + P.l * (w - w0) + P.m * w := rfl
    -- (b+c) p ≤ (b+c) ps + qs - q, (l+m) w ≥ (l+m) ws + q - qs
    have hp : (P.b + P.c) * p ≤ (P.b + P.c) * ps + (qs - q) := by nlinarith
    have hw : (P.l + P.m) * ws + (q - qs) ≤ (P.l + P.m) * w := by nlinarith
    have hp' : p ≤ ps + (qs - q) / (P.b + P.c) := by
      rw [← sub_le_iff_le_add', le_div_iff₀ hbc]; linarith
    have hw' : ws + (q - qs) / (P.l + P.m) ≤ w := by
      rw [← le_sub_iff_add_le', div_le_iff₀ hlm]; linarith
    have hmargin : p - w ≤ β * (2 * qs - q) := by
      have e : β * (2 * qs - q) = (ps - ws) + (qs - q) / (P.b + P.c) - (q - qs) / (P.l + P.m) := by
        rw [h3, hβ]; ring
      rw [e]; linarith
    by_cases hpw : p - w ≤ 0
    · have : (p - w) * q ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hpw hv.le
      have : 0 ≤ β * qs ^ 2 := by positivity
      linarith
    · have h4 : (p - w) * q ≤ β * (2 * qs - q) * q := mul_le_mul_of_nonneg_right hmargin hv.le
      have h5 : β * (2 * qs - q) * q ≤ β * qs ^ 2 := by
        have : 0 ≤ β * (q - qs) ^ 2 := by positivity
        nlinarith
      linarith

/-- The deviation on the line `d = s = q` against rival `(p0, w0)`. -/
private lemma dev_line (P : Params) (hb : 0 < P.b) (hc : 0 < P.c) (hl : 0 < P.l)
    (hm : 0 < P.m) (p0 w0 q : ℝ) (hq : 0 < q) :
    profit P ((P.a + P.b * p0 - q) / (P.b + P.c)) ((q + P.k + P.l * w0) / (P.l + P.m)) p0 w0 =
      ((P.a + P.b * p0 - q) / (P.b + P.c) - (q + P.k + P.l * w0) / (P.l + P.m)) * q := by
  have hbc : 0 < P.b + P.c := by linarith
  have hlm : 0 < P.l + P.m := by linarith
  have hd : demand P ((P.a + P.b * p0 - q) / (P.b + P.c)) p0 = q := by
    unfold demand; field_simp; ring
  have hs : supply P ((q + P.k + P.l * w0) / (P.l + P.m)) w0 = q := by
    unfold supply; field_simp; ring
  unfold profit volume
  rw [hd, hs, min_self, max_eq_right hq.le]

/-- A pair `(p, w)` with `p ≠ 0` is realized by the DCR action `(p, 1 - w/p)`. -/
private lemma dcrWage_realize (p w : ℝ) (hp : p ≠ 0) : dcrWage (p, 1 - w / p) = w := by
  unfold dcrWage; field_simp; ring

/-- If `β q₀² - β (q' - q₀)² ≤ π` for all `q' > 0` except one value, then `β q₀² ≤ π`. -/
private lemma lower_aux (β q₀ π C : ℝ) (hβ : 0 < β) (hq₀ : 0 < q₀)
    (h : ∀ q' : ℝ, 0 < q' → q' ≠ C → β * q₀ ^ 2 - β * (q' - q₀) ^ 2 ≤ π) :
    β * q₀ ^ 2 ≤ π := by
  by_contra hcon
  push_neg at hcon
  have hgap : 0 < β * q₀ ^ 2 - π := by linarith
  set t := min (q₀ / 2) ((β * q₀ ^ 2 - π) / (2 * β * q₀)) with ht
  have htpos : 0 < t := lt_min (by positivity) (by positivity)
  have ht1 : t ≤ q₀ / 2 := min_le_left _ _
  have ht2 : t ≤ (β * q₀ ^ 2 - π) / (2 * β * q₀) := min_le_right _ _
  clear_value t
  have hbt : β * t ^ 2 < β * q₀ ^ 2 - π := by
    have h1 : β * t * t ≤ β * t * (q₀ / 2) :=
      mul_le_mul_of_nonneg_left ht1 (by positivity)
    have h2 : β * t * (q₀ / 2) ≤ β * ((β * q₀ ^ 2 - π) / (2 * β * q₀)) * (q₀ / 2) := by
      have := mul_le_mul_of_nonneg_left ht2 hβ.le
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have h3 : β * ((β * q₀ ^ 2 - π) / (2 * β * q₀)) * (q₀ / 2) = (β * q₀ ^ 2 - π) / 4 := by
      have := hβ.ne'; have := hq₀.ne'
      field_simp; ring
    nlinarith
  by_cases hne : q₀ + t = C
  · have := h (q₀ - t) (by linarith) (by intro h2; linarith)
    have e : (q₀ - t - q₀) ^ 2 = t ^ 2 := by ring
    rw [e] at this; linarith
  · have := h (q₀ + t) (by linarith) hne
    have e : (q₀ + t - q₀) ^ 2 = t ^ 2 := by ring
    rw [e] at this; linarith

/-- Core of uniqueness: a symmetric profile `(p, w)` with positive demand and supply that no
realizable deviation beats has demand equal to supply and margin `β · volume`. -/
private lemma uniq_core (P : Params) (ha : 0 < P.a) (hb : 0 < P.b) (hc : 0 < P.c)
    (hl : 0 < P.l) (hm : 0 < P.m) (p w : ℝ)
    (hdpos : 0 < P.a - P.c * p) (hspos : 0 < -P.k + P.m * w)
    (hreal : ∀ p' w' : ℝ, p' ≠ 0 →
      profit P p' w' p w ≤ (p - w) * min (P.a - P.c * p) (-P.k + P.m * w)) :
    P.a - P.c * p = -P.k + P.m * w ∧
      p - w = (1 / (P.b + P.c) + 1 / (P.l + P.m)) * (P.a - P.c * p) := by
  have hbc : 0 < P.b + P.c := by linarith
  have hlm : 0 < P.l + P.m := by linarith
  set β := 1 / (P.b + P.c) + 1 / (P.l + P.m) with hβ
  have hβpos : 0 < β := by positivity
  set q := min (P.a - P.c * p) (-P.k + P.m * w) with hq
  have hqpos : 0 < q := lt_min hdpos hspos
  -- step 1: equilibrium profit is nonnegative
  have hπnn : 0 ≤ (p - w) * q := by
    set p' := max p (P.a / P.c) + 1 with hp'
    have hp'pos : p' ≠ 0 := by
      have : 0 < P.a / P.c := div_pos ha hc
      have : P.a / P.c ≤ max p (P.a / P.c) := le_max_right _ _
      intro h; linarith
    have h := hreal p' 0 hp'pos
    have hdneg : demand P p' p < 0 := by
      unfold demand
      have h1 : p ≤ p' := by have := le_max_left p (P.a / P.c); linarith
      have h2 : P.a / P.c < p' := by have := le_max_right p (P.a / P.c); linarith
      have h3 : P.a < P.c * p' := by rwa [div_lt_iff₀ hc, mul_comm] at h2
      nlinarith
    have : profit P p' 0 p w = 0 := by
      unfold profit volume
      rw [max_eq_left (le_trans (min_le_left _ _) hdneg.le), mul_zero]
    linarith
  -- step 2: margin bound along the realized point
  set M := (P.a + P.b * p - 0) / (P.b + P.c) - (0 + P.k + P.l * w) / (P.l + P.m) with hM
  have hupper : (p - w) * q ≤ (M - β * q) * q := by
    have hdq : q ≤ P.a - P.c * p := min_le_left _ _
    have hsq : q ≤ -P.k + P.m * w := min_le_right _ _
    have hp1 : p ≤ (P.a + P.b * p - q) / (P.b + P.c) := by
      rw [le_div_iff₀ hbc]; linarith
    have hw1 : (q + P.k + P.l * w) / (P.l + P.m) ≤ w := by
      rw [div_le_iff₀ hlm]; linarith
    have e : M - β * q = (P.a + P.b * p - q) / (P.b + P.c) - (q + P.k + P.l * w) / (P.l + P.m) := by
      rw [hM, hβ]; field_simp; ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (by linarith) hqpos.le
  -- the line deviations: value g(q') = (M - β q') q'
  have hline : ∀ q' : ℝ, 0 < q' → P.a + P.b * p - q' ≠ 0 → (M - β * q') * q' ≤ (p - w) * q := by
    intro q' hq' hne
    have hp' : (P.a + P.b * p - q') / (P.b + P.c) ≠ 0 := div_ne_zero hne hbc.ne'
    have h := hreal ((P.a + P.b * p - q') / (P.b + P.c)) ((q' + P.k + P.l * w) / (P.l + P.m)) hp'
    rw [dev_line P hb hc hl hm p w q' hq'] at h
    have e : M - β * q' = (P.a + P.b * p - q') / (P.b + P.c) - (q' + P.k + P.l * w) / (P.l + P.m) := by
      rw [hM, hβ]; field_simp; ring
    rw [e]; exact h
  -- M > 0
  have hMpos : 0 < M := by
    by_contra hcon; push_neg at hcon
    have : (M - β * q) * q < 0 := by
      apply mul_neg_of_neg_of_pos _ hqpos
      have : 0 < β * q := mul_pos hβpos hqpos
      linarith
    linarith
  set q₀ := M / (2 * β) with hq₀
  have hq₀pos : 0 < q₀ := by positivity
  have hM2 : M = 2 * β * q₀ := by rw [hq₀]; field_simp
  clear_value q₀ M
  -- lower bound: (p - w) q ≥ β q₀²
  have hlower : β * q₀ ^ 2 ≤ (p - w) * q := by
    apply lower_aux β q₀ ((p - w) * q) (P.a + P.b * p) hβpos hq₀pos
    intro q' hq' hne
    have h := hline q' hq' (fun h0 => hne (by linarith))
    have e : (M - β * q') * q' = β * q₀ ^ 2 - β * (q' - q₀) ^ 2 := by rw [hM2]; ring
    rw [e] at h; exact h
  -- squeeze
  have hsq0 : q = q₀ := by
    have h1 : (M - β * q) * q = β * q₀ ^ 2 - β * (q - q₀) ^ 2 := by rw [hM2]; ring
    have h2 : β * (q - q₀) ^ 2 ≤ 0 := by linarith
    have h3 : (q - q₀) ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc
      have := mul_pos hβpos hc; linarith
    have h4 : (q - q₀) ^ 2 = 0 := le_antisymm h3 (sq_nonneg _)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h4)
  have hmarg : p - w = β * q := by
    have h1 : (M - β * q) * q = β * q₀ ^ 2 := by rw [hM2, hsq0]; ring
    have h2 : (p - w) * q = β * q * q := by
      have : β * q₀ ^ 2 = β * q * q := by rw [hsq0]; ring
      linarith
    exact mul_right_cancel₀ hqpos.ne' h2
  -- d = s = q
  have hdq : q ≤ P.a - P.c * p := min_le_left _ _
  have hsq : q ≤ -P.k + P.m * w := min_le_right _ _
  have hMq : p - w = M - β * q := by rw [hmarg, hM2, hsq0]; ring
  have hd_eq : P.a - P.c * p = q := by
    have e : M - β * q = (P.a + P.b * p - q) / (P.b + P.c) - (q + P.k + P.l * w) / (P.l + P.m) := by
      rw [hM, hβ]; field_simp; ring
    have hp1 : p ≤ (P.a + P.b * p - q) / (P.b + P.c) := by
      rw [le_div_iff₀ hbc]; linarith
    have hw1 : (q + P.k + P.l * w) / (P.l + P.m) ≤ w := by
      rw [div_le_iff₀ hlm]; linarith
    have hpe : p = (P.a + P.b * p - q) / (P.b + P.c) := by linarith
    rw [eq_div_iff hbc.ne'] at hpe
    linarith
  have hs_eq : -P.k + P.m * w = q := by
    have e : M - β * q = (P.a + P.b * p - q) / (P.b + P.c) - (q + P.k + P.l * w) / (P.l + P.m) := by
      rw [hM, hβ]; field_simp; ring
    have hp1 : p = (P.a + P.b * p - q) / (P.b + P.c) := by
      rw [eq_div_iff hbc.ne']; linarith
    have hwe : w = (q + P.k + P.l * w) / (P.l + P.m) := by linarith
    rw [eq_div_iff hlm.ne'] at hwe
    linarith
  constructor
  · linarith
  · rw [hmarg, hd_eq]

private lemma lin_uniq (a c k m β p w p' w' : ℝ) (hc : 0 < c) (hm : 0 < m) (hβ : 0 < β)
    (E1 : a - c * p = -k + m * w) (E2 : p - w = β * (a - c * p))
    (F1 : a - c * p' = -k + m * w') (F2 : p' - w' = β * (a - c * p')) : p = p' ∧ w = w' := by
  have h : (p - p') * (c + m * (1 + β * c)) = 0 := by
    linear_combination (-1 : ℝ) * E1 + F1 + m * E2 - m * F2
  have hpos : 0 < c + m * (1 + β * c) := by positivity
  have hX := (mul_eq_zero.mp h).resolve_right hpos.ne'
  constructor
  · linarith
  · have : w - w' = (p - p') * (1 + β * c) := by linear_combination (-1 : ℝ) * E2 + F2
    rw [hX, zero_mul] at this
    linarith

theorem solution (P : Params) (hP : P.Standing) :
    IsNashDCR P (pD P, alphaD P) (pD P, alphaD P) ∧
    NontrivialDCR P (pD P, alphaD P) (pD P, alphaD P) ∧
    0 < alphaD P ∧ alphaD P < 1 ∧
    ∀ x : ℝ × ℝ, IsNashDCR P x x → NontrivialDCR P x x → x = (pD P, alphaD P) := by
  have hP' := hP
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  have ham : 0 < P.a * P.m - P.c * P.k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  have hbc : 0 < P.b + P.c := by linarith
  have hlm : 0 < P.l + P.m := by linarith
  set β := 1 / (P.b + P.c) + 1 / (P.l + P.m) with hβ
  have hβpos : 0 < β := by positivity
  -- closed-form facts
  have hNa : 0 < P.k * (P.b + P.c) * (P.l + P.m) +
      P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m)) := by
    have h1 : 0 < P.k * (P.b + P.c) * (P.l + P.m) := by positivity
    have h2 : 0 < P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m)) := by positivity
    linarith
  have hDp : 0 < P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m) := by
    positivity
  have hpD : 0 < pD P := by unfold pD; exact div_pos hNa hDp
  have hqD : P.a - P.c * pD P = (P.b + P.c) * (P.l + P.m) * (P.a * P.m - P.c * P.k) /
      (P.c * (P.b + P.c) * (P.l + 2 * P.m) + P.m * (P.b + 2 * P.c) * (P.l + P.m)) := by
    unfold pD
    rw [eq_div_iff hDp.ne']
    field_simp
    ring
  have hqDpos : 0 < P.a - P.c * pD P := by rw [hqD]; positivity
  have hDid : P.a - P.c * pD P = -P.k + P.m * ((1 - alphaD P) * pD P) := by
    unfold pD alphaD
    field_simp
    ring
  have hFOC : pD P - (1 - alphaD P) * pD P = β * (P.a - P.c * pD P) := by
    rw [hβ]
    unfold pD alphaD
    field_simp
    ring
  have hαD0 : 0 < alphaD P := by
    unfold alphaD
    apply div_pos _ hNa
    have : 0 < P.b + P.c + P.l + P.m := by linarith
    positivity
  have hαD1 : alphaD P < 1 := by
    have h : 1 - alphaD P = (P.a * P.b * P.l + P.a * P.b * P.m + P.a * P.c * P.l +
        P.a * P.c * P.m + P.b * P.c * P.k + P.b * P.k * P.l + P.b * P.k * P.m + P.c ^ 2 * P.k +
        2 * P.c * P.k * P.l + 2 * P.c * P.k * P.m) /
        (P.k * (P.b + P.c) * (P.l + P.m) +
          P.a * (P.m * (P.l + P.m) + (P.b + P.c) * (P.l + 2 * P.m))) := by
      unfold alphaD
      rw [eq_div_iff hNa.ne']
      field_simp
      ring
    have : 0 < 1 - alphaD P := by rw [h]; positivity
    linarith
  -- existence
  set wD := (1 - alphaD P) * pD P with hwD
  set qD := P.a - P.c * pD P with hqDdef
  have hsymD : profitDCR P (pD P, alphaD P) (pD P, alphaD P) = β * qD ^ 2 := by
    unfold profitDCR dcrWage profit volume demand supply
    simp only
    rw [← hwD]
    have e1 : P.a - P.b * (pD P - pD P) - P.c * pD P = qD := by ring
    have e2 : -P.k + P.l * (wD - wD) + P.m * wD = qD := by rw [hDid]; ring
    rw [e1, e2, min_self, max_eq_right hqDpos.le, hFOC]
    ring
  have hNash : ∀ y : ℝ × ℝ, profitDCR P y (pD P, alphaD P) ≤
      profitDCR P (pD P, alphaD P) (pD P, alphaD P) := by
    intro y
    rw [hsymD]
    unfold profitDCR
    exact dev_upper P hb hc hl hm (pD P) wD (pD P) wD qD y.1 (dcrWage y)
      (by rw [hqDdef]; ring) (by linarith [hDid, hqDdef]) hFOC
  refine ⟨⟨hNash, hNash⟩, ?_, hαD0, hαD1, ?_⟩
  · have h1 : 0 < demand P (pD P) (pD P) := by
      unfold demand
      have := hqDpos
      rw [hqDdef] at this
      linarith [show P.b * (pD P - pD P) = 0 by ring]
    have h2 : 0 < supply P (dcrWage (pD P, alphaD P)) (dcrWage (pD P, alphaD P)) := by
      unfold supply dcrWage; simp only; rw [← hwD]; nlinarith [hDid]
    exact ⟨h1, h2, h1, h2⟩
  -- uniqueness
  intro x hx hxn
  obtain ⟨p, α⟩ := x
  set w := (1 - α) * p with hw
  have hdx : demand P p p = P.a - P.c * p := by unfold demand; ring
  have hsx : supply P w w = -P.k + P.m * w := by unfold supply; ring
  have hdpos : 0 < P.a - P.c * p := by
    have := hxn.1; rw [hdx] at this; exact this
  have hspos : 0 < -P.k + P.m * w := by
    have := hxn.2.1; unfold dcrWage at this; simp only at this; rw [← hw, hsx] at this
    exact this
  set q := min (P.a - P.c * p) (-P.k + P.m * w) with hq
  have hqpos : 0 < q := lt_min hdpos hspos
  have hπ : profitDCR P (p, α) (p, α) = (p - w) * q := by
    unfold profitDCR dcrWage profit volume
    simp only
    rw [← hw, hdx, hsx, max_eq_right hqpos.le]
  have hdev : ∀ y : ℝ × ℝ, profit P y.1 (dcrWage y) p w ≤ (p - w) * q := by
    intro y
    have := hx.1 y
    unfold profitDCR at this
    simp only [dcrWage] at this ⊢
    rw [← hw] at this
    rw [← hπ]
    unfold profitDCR dcrWage
    simpa using this
  -- realized deviations
  have hreal : ∀ p' w' : ℝ, p' ≠ 0 → profit P p' w' p w ≤ (p - w) * q := by
    intro p' w' hp'
    have := hdev (p', 1 - w' / p')
    rw [dcrWage_realize p' w' hp'] at this
    exact this
  obtain ⟨E1, E2⟩ := uniq_core P ha hb hc hl hm p w hdpos hspos hreal
  -- solve the linear system
  have F1 : P.a - P.c * pD P = -P.k + P.m * wD := hDid
  have F2 : pD P - wD = β * (P.a - P.c * pD P) := hFOC
  obtain ⟨hpp, hww⟩ := lin_uniq P.a P.c P.k P.m β p w (pD P) wD hc hm hβpos E1 E2 F1 F2
  have hαα : α = alphaD P := by
    rw [hw, hwD, hpp] at hww
    have := mul_right_cancel₀ hpD.ne' hww
    linarith
  rw [hpp, hαα]
