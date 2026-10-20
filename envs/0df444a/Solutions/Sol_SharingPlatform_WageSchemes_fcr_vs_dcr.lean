-- Prove2me | solution 1 for SharingPlatform.WageSchemes.fcr_vs_dcr
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T03:40:40.594982+00:00
-- url     : https://prove2.me/submissions/b2a579a9-0b63-4d86-83e8-450f9170837f

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

theorem solution (P : Params) (hP : P.Standing) (hcl : P.c * P.l ≠ P.b * P.m)
    (α : ℝ) (hα : α ∈ Set.Ioo (alphaBar P) 1) (hf : fFCR P α = 0) :
    (alphaD P < α ↔ 0 < cond13 P (alphaD P)) ∧
    (α < alphaD P ↔ cond13 P (alphaD P) < 0) ∧
    (pD P < priceFCR P α ↔ alphaD P < α) := by
  have hP' := hP
  have hα1 : α < 1 := hα.2
  obtain ⟨a, b, c, k, l, m⟩ := P
  obtain ⟨ha, hb, hc, hk, hl, hm, hA1, hA2⟩ := hP
  dsimp only at ha hb hc hk hl hm hA1 hA2 hcl
  have ham : 0 < a * m - c * k := by
    rw [div_lt_div_iff₀ hm hc] at hA1; linarith
  have hbc : b * m - c * l ≠ 0 := fun h => hcl (by linarith)
  have hcb : c * l - b * m ≠ 0 := fun h => hcl (by linarith)
  set Na := k * (b + c) * (l + m) + a * (m * (l + m) + (b + c) * (l + 2 * m)) with hNa
  have hNapos : 0 < Na := by positivity
  set H := a*b*l + a*b*m + a*c*l + a*c*m + b*c*k + b*k*l + b*k*m + c^2*k + 2*c*k*l +
    2*c*k*m with hH
  have hHpos : 0 < H := by positivity
  have hnD : 0 < (b + c + l + m) * (a * m - c * k) := by positivity
  have hαD : alphaD ⟨a, b, c, k, l, m⟩ = (b + c + l + m) * (a * m - c * k) / Na := by
    rw [hNa]; rfl
  have hαD0 : 0 < alphaD ⟨a, b, c, k, l, m⟩ := by rw [hαD]; positivity
  have h1αD : 1 - alphaD ⟨a, b, c, k, l, m⟩ = H / Na := by
    rw [hαD, eq_div_iff hNapos.ne']
    field_simp
    ring
  have hαD1 : alphaD ⟨a, b, c, k, l, m⟩ < 1 := by
    have : 0 < H / Na := by positivity
    linarith
  set R := 2*a*b^2*l*m + 2*a*b^2*m^2 - a*b*c*l^2 + a*b*c*l*m + 2*a*b*c*m^2 + a*b*l^2*m +
    2*a*b*l*m^2 + a*b*m^3 - a*c^2*l^2 - a*c^2*l*m - b^2*c*k*l + b^2*k*l*m + b^2*k*m^2 -
    2*b*c^2*k*l - 2*b*c*k*l^2 - b*c*k*l*m + b*c*k*m^2 - c^3*k*l - 2*c^2*k*l^2 -
    2*c^2*k*l*m with hR
  set G := a*b*l + 2*a*b*m + a*c*l + 2*a*c*m + b*k*l + b*k*m + 2*c*k*l + 2*c*k*m with hG
  have hGpos : 0 < G := by positivity
  set T := R * (b * m - c * l) with hT
  have hfD : fFCR ⟨a, b, c, k, l, m⟩ (alphaD ⟨a, b, c, k, l, m⟩) =
      (a + k) * (a * m - c * k) * T / Na ^ 2 := by
    rw [hαD]
    simp only [fFCR]
    rw [eq_div_iff (by positivity)]
    field_simp
    ring
  have hE : 0 < (b + c) * (l + m) * (a * m - c * k) * (b * m - c * l) ^ 2 * H := by
    have : 0 < (b * m - c * l) ^ 2 := by positivity
    positivity
  have hQ : cond13 ⟨a, b, c, k, l, m⟩ (alphaD ⟨a, b, c, k, l, m⟩) =
      G * T / ((b + c) * (l + m) * (a * m - c * k) * (b * m - c * l) ^ 2 * H) := by
    simp only [cond13]
    rw [h1αD, hαD]
    have hH' := hHpos.ne'
    have e1 : (b + c + l + m) / ((b + c) * (l + m) * ((b + c + l + m) * (a * m - c * k) / Na)) =
        Na / ((b + c) * (l + m) * (a * m - c * k)) := by
      rw [div_eq_div_iff (by positivity) (by positivity)]
      field_simp
    have e2 : (b + H / Na * l) / (H / Na * (c * l - b * m)) = (b * Na + H * l) / (H * (c * l - b * m)) := by
      rw [div_eq_div_iff (mul_ne_zero (by positivity) hcb) (mul_ne_zero hH' hcb)]
      field_simp
    rw [e1, e2, div_sub_div _ _ (by positivity) (mul_ne_zero hH' hcb),
      div_eq_div_iff (mul_ne_zero (by positivity) (mul_ne_zero hH' hcb)) hE.ne']
    rw [hT, hR, hG, hNa, hH]
    ring
  have hK1 : 0 < (a + k) * (a * m - c * k) := by positivity
  have hNa2 : 0 < Na ^ 2 := by positivity
  have hq := quad_pos_iff _ hP' α _ hα1 hf hαD1
  refine ⟨?_, ?_, ?_⟩
  · rw [hq.1, hfD, hQ, div_pos_iff_of_pos_right hNa2, div_pos_iff_of_pos_right hE,
      mul_pos_iff_of_pos_left hK1, mul_pos_iff_of_pos_left hGpos]
  · rw [hq.2, hfD, hQ, div_neg_iff, div_neg_iff]
    constructor
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · right
        refine ⟨?_, hE⟩
        by_contra hcon; push_neg at hcon
        have hT0 : 0 ≤ T := by
          by_contra hT0; push_neg at hT0
          have := mul_neg_of_pos_of_neg hGpos hT0; linarith
        have := mul_nonneg hK1.le hT0; linarith
    · rintro (⟨-, h⟩ | ⟨h, -⟩)
      · linarith
      · right
        refine ⟨?_, hNa2⟩
        have hT0 : T < 0 := by
          by_contra hT0; push_neg at hT0
          have := mul_nonneg hGpos.le hT0; linarith
        exact mul_neg_of_pos_of_neg hK1 hT0
  · have hden : 0 < c + m * (1 - alphaD ⟨a, b, c, k, l, m⟩) := by
      have := mul_pos hm (sub_pos.2 hαD1); linarith
    have hDp : 0 < c * (b + c) * (l + 2 * m) + m * (b + 2 * c) * (l + m) := by positivity
    have hpDeq : pD ⟨a, b, c, k, l, m⟩ = priceFCR ⟨a, b, c, k, l, m⟩ (alphaD ⟨a, b, c, k, l, m⟩) := by
      simp only [priceFCR]
      rw [eq_div_iff hden.ne', h1αD]
      simp only [pD]
      field_simp
      ring
    rw [hpDeq]
    exact (priceFCR_strictMono _ hP').lt_iff_lt (Set.mem_Iic.2 hαD1.le) (Set.mem_Iic.2 hα1.le)
