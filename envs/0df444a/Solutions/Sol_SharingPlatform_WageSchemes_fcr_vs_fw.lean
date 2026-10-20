-- Prove2me | solution 1 for SharingPlatform.WageSchemes.fcr_vs_fw
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:36:58.957155+00:00
-- url     : https://prove2.me/submissions/94f59f8e-7dc5-4464-aa39-719575246b19

import Mathlib
import Definitions.Def_SharingPlatform_WageSchemes_Model

open SharingPlatform.WageSchemes

/-- Sign of the FCR quadratic `f` relative to a zero `α < 1`: by convexity and `f(1) < 0`. -/
private lemma quad_sign (P : Params) (hP : P.Standing) (α x : ℝ) (hα1 : α < 1)
    (hf : fFCR P α = 0) (hx : x < 1) :
    (x < α → 0 < fFCR P x) ∧ (α < x → fFCR P x < 0) := by
  obtain ⟨a, b, c, k, l, m⟩ := P
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  dsimp only at ha hb hc hk hl hm hA1 hA2
  set A := m * (a + k) * (b + c) * (2 * l + m) +
    a * m * (m * (b + 2 * l + m) + c * (l + m)) with hA
  have hApos : 0 < A := by positivity
  have hF1 : fFCR ⟨a, b, c, k, l, m⟩ 1 = -c * (2*a*b*l + 2*a*b*m + a*c*l + a*c*m + 2*b*c*k +
      2*b*k*l + 3*b*k*m + c^2*k + 2*c*k*l + 2*c*k*m) := by
    simp only [fFCR]; ring
  have hF1neg : fFCR ⟨a, b, c, k, l, m⟩ 1 < 0 := by
    rw [hF1]
    have : 0 < c * (2*a*b*l + 2*a*b*m + a*c*l + a*c*m + 2*b*c*k +
      2*b*k*l + 3*b*k*m + c^2*k + 2*c*k*l + 2*c*k*m) := by positivity
    linarith
  have interp : ∀ u y z : ℝ, (z - u) * fFCR ⟨a, b, c, k, l, m⟩ y =
      (z - y) * fFCR ⟨a, b, c, k, l, m⟩ u + (y - u) * fFCR ⟨a, b, c, k, l, m⟩ z +
        A * (y - u) * (y - z) * (z - u) := by
    intro u y z; simp only [fFCR, hA]; ring
  constructor
  · intro hxα
    have h := interp x α 1
    rw [hf, mul_zero] at h
    have t2 : (α - x) * fFCR ⟨a, b, c, k, l, m⟩ 1 < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hF1neg
    have t3 : A * (α - x) * (α - 1) * (1 - x) < 0 := by
      have h1 : 0 < A * (α - x) := mul_pos hApos (by linarith)
      have h2 : A * (α - x) * (α - 1) < 0 := mul_neg_of_pos_of_neg h1 (by linarith)
      exact mul_neg_of_neg_of_pos h2 (by linarith)
    by_contra hcon
    push_neg at hcon
    have : (1 - α) * fFCR ⟨a, b, c, k, l, m⟩ x ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hcon
    linarith
  · intro hαx
    have h := interp α x 1
    rw [hf, mul_zero] at h
    have t2 : (x - α) * fFCR ⟨a, b, c, k, l, m⟩ 1 < 0 :=
      mul_neg_of_pos_of_neg (by linarith) hF1neg
    have t3 : A * (x - α) * (x - 1) * (1 - α) < 0 := by
      have h1 : 0 < A * (x - α) := mul_pos hApos (by linarith)
      have h2 : A * (x - α) * (x - 1) < 0 := mul_neg_of_pos_of_neg h1 (by linarith)
      exact mul_neg_of_neg_of_pos h2 (by linarith)
    by_contra hcon
    push_neg at hcon
    have : 0 ≤ (1 - α) * fFCR ⟨a, b, c, k, l, m⟩ x := mul_nonneg (by linarith) hcon
    linarith

/-- Position of `x < 1` relative to the zero `α < 1` is read off the sign of `f(x)`. -/
private lemma quad_pos_iff (P : Params) (hP : P.Standing) (α x : ℝ) (hα1 : α < 1)
    (hf : fFCR P α = 0) (hx : x < 1) :
    (x < α ↔ 0 < fFCR P x) ∧ (α < x ↔ fFCR P x < 0) := by
  have hs := quad_sign P hP α x hα1 hf hx
  constructor
  · refine ⟨hs.1, fun h => ?_⟩
    rcases lt_trichotomy x α with h' | h' | h'
    · exact h'
    · rw [h', hf] at h; exact absurd h (lt_irrefl 0)
    · have := hs.2 h'; linarith
  · refine ⟨hs.2, fun h => ?_⟩
    rcases lt_trichotomy x α with h' | h' | h'
    · have := hs.1 h'; linarith
    · rw [h', hf] at h; exact absurd h (lt_irrefl 0)
    · exact h'

/-- The FCR price formula is strictly increasing on `(-∞, 1]`. -/
private lemma priceFCR_strictMono (P : Params) (hP : P.Standing) :
    StrictMonoOn (priceFCR P) (Set.Iic 1) := by
  obtain ⟨ha, hb, hc, hk, hl, hm, -, -⟩ := hP
  intro β hβ γ hγ hβγ
  simp only [Set.mem_Iic] at hβ hγ
  unfold priceFCR
  have hγ' : 0 < P.c + P.m * (1 - γ) := by
    have := mul_nonneg hm.le (sub_nonneg.2 hγ); linarith
  apply div_lt_div_of_pos_left (by linarith) hγ'
  have := mul_lt_mul_of_pos_left (show 1 - γ < 1 - β by linarith) hm
  linarith

theorem solution (P : Params) (hP : P.Standing)
    (α : ℝ) (hα : α ∈ Set.Ioo (alphaBar P) 1) (hf : fFCR P α = 0) :
    (alphaW P < α ↔ P.b * P.m < P.c * P.l) ∧
    (α < alphaW P ↔ P.c * P.l < P.b * P.m) ∧
    (pW P < priceFCR P α ↔ alphaW P < α) := by
  have hP' := hP
  have hα1 : α < 1 := hα.2
  obtain ⟨a, b, c, k, l, m⟩ := P
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  dsimp only at ha hb hc hk hl hm hA1 hA2
  have ham : 0 < a * m - c * k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  set NW := 2*a*b*c*l + 4*a*b*c*m + a*b*m^2 + a*c^2*l + 2*a*c^2*m + a*c*l*m + a*c*m^2 +
    2*b*c*k*l + 2*b*c*k*m + c^2*k*l + c^2*k*m with hNW
  have hNWpos : 0 < NW := by positivity
  have hDW : 0 < b * (2 * c * (l + 2 * m) + m * (2 * l + 3 * m)) +
      c * (c * (l + 2 * m) + 2 * m * (l + m)) := by positivity
  have hwW : 0 < wW ⟨a, b, c, k, l, m⟩ := by simp only [wW]; positivity
  have hpWf : pW ⟨a, b, c, k, l, m⟩ = NW / (c * (b * (2 * c * (l + 2 * m) +
      m * (2 * l + 3 * m)) + c * (c * (l + 2 * m) + 2 * m * (l + m)))) := by
    simp only [pW, wW]
    rw [eq_div_iff (by positivity)]
    field_simp
    ring
  have hpW : 0 < pW ⟨a, b, c, k, l, m⟩ := by rw [hpWf]; positivity
  have hcpW : c * pW ⟨a, b, c, k, l, m⟩ = a + k - m * wW ⟨a, b, c, k, l, m⟩ := by
    simp only [pW]; field_simp
  have hαW1 : alphaW ⟨a, b, c, k, l, m⟩ < 1 := by
    simp only [alphaW]
    have := div_pos hwW hpW
    linarith
  have hαWf : alphaW ⟨a, b, c, k, l, m⟩ =
      (a * m - c * k) * (2 * b * c + b * m + c ^ 2 + c * l + c * m) / NW := by
    simp only [alphaW]
    rw [hpWf]
    simp only [wW]
    rw [eq_div_iff hNWpos.ne']
    field_simp
    ring
  set R := (2*b*c*l + 2*b*l*m + b*m^2 + c^2*l) *
    (2*a*b*l + 2*a*b*m + a*c*l + a*c*m + 2*b*c*k + 2*b*k*l + 3*b*k*m + c^2*k + 2*c*k*l +
      2*c*k*m) with hR
  have hRpos : 0 < R := by positivity
  have hfW : fFCR ⟨a, b, c, k, l, m⟩ (alphaW ⟨a, b, c, k, l, m⟩) =
      -(c * (a + k) * (a * m - c * k) * R) * (b * m - c * l) / NW ^ 2 := by
    rw [hαWf]
    simp only [fFCR]
    rw [eq_div_iff (by positivity)]
    field_simp
    ring
  have hK : 0 < c * (a + k) * (a * m - c * k) * R := by positivity
  have hNW2 : 0 < NW ^ 2 := by positivity
  have hq := quad_pos_iff _ hP' α _ hα1 hf hαW1
  have hnK : -(c * (a + k) * (a * m - c * k) * R) < 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hq.1, hfW, div_pos_iff_of_pos_right hNW2]
    constructor
    · intro h
      by_contra hcon; push_neg at hcon
      have : -(c * (a + k) * (a * m - c * k) * R) * (b * m - c * l) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hnK.le (by linarith)
      linarith
    · intro h
      exact mul_pos_of_neg_of_neg hnK (by linarith)
  · rw [hq.2, hfW, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · by_contra hcon; push_neg at hcon
        have : 0 ≤ -(c * (a + k) * (a * m - c * k) * R) * (b * m - c * l) :=
          mul_nonneg_of_nonpos_of_nonpos hnK.le (by linarith)
        linarith
    · intro h
      right
      exact ⟨mul_neg_of_neg_of_pos hnK (by linarith), hNW2⟩
  · have hpWeq : pW ⟨a, b, c, k, l, m⟩ = priceFCR ⟨a, b, c, k, l, m⟩ (alphaW ⟨a, b, c, k, l, m⟩) := by
      have hden : 0 < c + m * (1 - alphaW ⟨a, b, c, k, l, m⟩) := by
        have := mul_pos hm (sub_pos.2 hαW1); linarith
      simp only [priceFCR]
      rw [eq_div_iff hden.ne']
      have h1 : 1 - alphaW ⟨a, b, c, k, l, m⟩ = wW ⟨a, b, c, k, l, m⟩ / pW ⟨a, b, c, k, l, m⟩ := by
        simp only [alphaW]; ring
      rw [h1]
      have hne := hpW.ne'
      field_simp
      linarith
    rw [hpWeq]
    exact (priceFCR_strictMono _ hP').lt_iff_lt (Set.mem_Iic.2 hαW1.le) (Set.mem_Iic.2 hα1.le)
