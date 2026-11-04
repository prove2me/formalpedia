-- Prove2me | solution 1 for SolarNonOwn.BizChoice.crossing_high_alpha
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T10:30:58.525724+00:00
-- url     : https://prove2.me/submissions/e452a0b1-152b-4d60-928d-df098ff3f983

import Mathlib
import Definitions.Def_SolarNonOwn_BizChoice_ClosedForms

noncomputable section
open SolarNonOwn.BizChoice

private lemma quad_piece (G : ℝ → ℝ) (k2 k1 lo hi : ℝ)
    (hG : ∀ x y, G y - G x = (y - x) * (k2 * (x + y) + k1))
    (hlo : 2 * k2 * lo + k1 < 0) (hhi : 2 * k2 * hi + k1 < 0) :
    StrictAntiOn G (Set.Icc lo hi) := by
  intro x hx y hy hxy
  have hL : k2 * (x + y) + k1 < 0 := by
    rcases le_or_gt 0 k2 with h | h
    · have : k2 * (x + y) ≤ k2 * (2 * hi) :=
        mul_le_mul_of_nonneg_left (by linarith [hx.2, hy.2]) h
      linarith
    · have : k2 * (x + y) ≤ k2 * (2 * lo) :=
        mul_le_mul_of_nonpos_left (by linarith [hx.1, hy.1]) h.le
      linarith
  have := hG x y
  have : (y - x) * (k2 * (x + y) + k1) < 0 := mul_neg_of_pos_of_neg (by linarith) hL
  linarith

private lemma hi_G1 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    ∀ x y : ℝ, (profA1 (⟨a, b, r, t, g⟩ : Params) y - profB1 (⟨a, b, r, t, g⟩ : Params) y) - (profA1 (⟨a, b, r, t, g⟩ : Params) x - profB1 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * ((-(1-a)^2*(2*a*b+2*a*r+b+r+t)/(4*g*(r+b)*(r + t + a * (r - t) + b * (1 + a)))) * (x + y) + (-(1-a)*(b+r+t)/(2*(r + t + a * (r - t) + b * (1 + a))))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  intro x y
  simp only [profA1, profB1, prof0star]
  field_simp
  ring

private lemma hi_G2 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    ∀ x y : ℝ, (profA2 (⟨a, b, r, t, g⟩ : Params) y - profB1 (⟨a, b, r, t, g⟩ : Params) y) - (profA2 (⟨a, b, r, t, g⟩ : Params) x - profB1 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * ((-(a-1)*(2*a^3*b*r+2*a^3*b*t+2*a^3*r^2+2*a^3*r*t-3*a^2*b*r-3*a^2*b*t-3*a^2*r^2-2*a^2*r*t+b*r+b*t)/(4*g*(r+b)*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * (x + y) + ((a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*r-2*a*b*t+b*r+b*t)/(2*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2))))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  intro x y
  simp only [profA2, denomA2, profB1, prof0star]
  field_simp
  ring

private lemma hi_G3 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    ∀ x y : ℝ, (profA3 (⟨a, b, r, t, g⟩ : Params) y - profB1 (⟨a, b, r, t, g⟩ : Params) y) - (profA3 (⟨a, b, r, t, g⟩ : Params) x - profB1 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * (((a-1)/(4*g*(r+b))) * (x + y) + ((2*a-1)/2)) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  intro x y
  simp only [profA3, profB1, prof0star]
  field_simp
  ring

private lemma hi_e1hi (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    2 * (-(1-a)^2*(2*a*b+2*a*r+b+r+t)/(4*g*(r+b)*(r + t + a * (r - t) + b * (1 + a)))) * CA1 (⟨a, b, r, t, g⟩ : Params) + (-(1-a)*(b+r+t)/(2*(r + t + a * (r - t) + b * (1 + a)))) = ((a-1)*(2*a*b*r+a*b*t+2*a*r^2+a*r*t-b*t)/(2*a*(r+b)*(r+t*(1-a)))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [CA1]
  field_simp
  ring

private lemma hi_e2lo (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    2 * (-(a-1)*(2*a^3*b*r+2*a^3*b*t+2*a^3*r^2+2*a^3*r*t-3*a^2*b*r-3*a^2*b*t-3*a^2*r^2-2*a^2*r*t+b*r+b*t)/(4*g*(r+b)*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * CA1 (⟨a, b, r, t, g⟩ : Params) + ((a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*r-2*a*b*t+b*r+b*t)/(2*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) = ((a-1)*(2*a*b*r+a*b*t+2*a*r^2+a*r*t-b*t)/(2*a*(r+b)*(r+t*(1-a)))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [CA1]
  field_simp
  ring

private lemma hi_e2hi (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    2 * (-(a-1)*(2*a^3*b*r+2*a^3*b*t+2*a^3*r^2+2*a^3*r*t-3*a^2*b*r-3*a^2*b*t-3*a^2*r^2-2*a^2*r*t+b*r+b*t)/(4*g*(r+b)*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * CA2 (⟨a, b, r, t, g⟩ : Params) + ((a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*r-2*a*b*t+b*r+b*t)/(2*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) = ((2*a*(b+r)*(r+t) - 2*(b+r)*(r+t) + r*t)/(2*(r+b)*(r+t))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [CA2]
  field_simp
  ring

private lemma hi_e3lo (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    2 * ((a-1)/(4*g*(r+b))) * CA2 (⟨a, b, r, t, g⟩ : Params) + ((2*a-1)/2) = ((2*a*(b+r)*(r+t) - 2*(b+r)*(r+t) + r*t)/(2*(r+b)*(r+t))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [CA2]
  field_simp
  ring

private lemma hi_e3hi (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    2 * ((a-1)/(4*g*(r+b))) * C0 (⟨a, b, r, t, g⟩ : Params) + ((2*a-1)/2) = (a - 1) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [C0]
  field_simp
  ring

private lemma hi_cont1 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    profA1 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) = profA2 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [profA1, profA2, denomA2, CA1]
  field_simp
  ring

private lemma hi_cont2 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    profA2 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) = profA3 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [profA2, profA3, denomA2, CA2]
  field_simp
  ring

private lemma hi_val0 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    profA1 (⟨a, b, r, t, g⟩ : Params) 0 - profB1 (⟨a, b, r, t, g⟩ : Params) 0 = g*(b+r)*(b+r-t)/(4*(r + t + a * (r - t) + b * (1 + a))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [profA1, profB1, prof0star]
  field_simp
  ring

private lemma hi_valCA1 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    profA1 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) - profB1 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) = -g*(-a^3*b^2*t^2 - 2*a^3*b*r*t^2 - a^3*r^2*t^2 + 2*a^2*b^2*r^2 + 4*a^2*b^2*r*t + 3*a^2*b^2*t^2 + 4*a^2*b*r^3 + 6*a^2*b*r^2*t + 4*a^2*b*r*t^2 + 2*a^2*r^4 + 2*a^2*r^3*t + a^2*r^2*t^2 - 4*a*b^2*r*t - 3*a*b^2*t^2 - 4*a*b*r^2*t - 2*a*b*r*t^2 + b^2*t^2)/(4*a^2*(r+b)*(r+t*(1-a))^2) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [profA1, profB1, prof0star, CA1]
  field_simp
  ring

private lemma hi_ord12 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    CA2 (⟨a, b, r, t, g⟩ : Params) - CA1 (⟨a, b, r, t, g⟩ : Params) = g*t*(-(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t))/(a*(1-a)*(r+t)*(r+t*(1-a))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [CA1, CA2]
  field_simp
  ring

private lemma hi_ord20 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    C0 (⟨a, b, r, t, g⟩ : Params) - CA2 (⟨a, b, r, t, g⟩ : Params) = g*r*t/((1-a)*(r+t)) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [C0, CA2]
  field_simp
  ring

private lemma hi_ord10 (a b r t g : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hg0 : 0 < g) (hbr : b < r) (ha1 : a < 1) (hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t))  :
    C0 (⟨a, b, r, t, g⟩ : Params) - CA1 (⟨a, b, r, t, g⟩ : Params) = g*t*(a*b+a*r+b)/(a*(r+t*(1-a))) := by
  have hr0 : 0 < r := lt_trans ht0 htr
  have h1a : 0 < 1 - a := by linarith
  have hE : 0 < a*b+a*r-a*t+b+r+t := by nlinarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hR2 : 0 < r + t - a * t := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := by nlinarith
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by nlinarith
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := hR2.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  simp only [C0, CA1]
  field_simp
  ring
private lemma hi_N_pos (a b r t : ℝ) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (ha1 : a < 1) (hA2 : b ≤ a * (b + r)) :
    0 < (-a^3*b^2*t^2 - 2*a^3*b*r*t^2 - a^3*r^2*t^2 + 2*a^2*b^2*r^2 + 4*a^2*b^2*r*t + 3*a^2*b^2*t^2 + 4*a^2*b*r^3 + 6*a^2*b*r^2*t + 4*a^2*b*r*t^2 + 2*a^2*r^4 + 2*a^2*r^3*t + a^2*r^2*t^2 - 4*a*b^2*r*t - 3*a*b^2*t^2 - 4*a*b*r^2*t - 2*a*b*r*t^2 + b^2*t^2) := by
  obtain ⟨u, hu⟩ : ∃ u, u = a * (b + r) - b := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = r - t := ⟨_, rfl⟩
  have hu0 : 0 ≤ u := by rw [hu]; linarith
  have hv0 : 0 < v := by rw [hv]; linarith
  have hur : 0 < r - u := by rw [hu]; nlinarith
  obtain ⟨w, hw⟩ : ∃ w, w = r - u := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; exact hur
  have hr0 : 0 < r := by linarith
  have hQ : 0 < 2*b^3*t^2 + 4*b^3*t*v + 2*b^3*v^2 + 8*b^2*t^2*u + 2*b^2*t^2*v + 12*b^2*t*u*v + 4*b^2*t*v^2 + 4*b^2*u*v^2 + 2*b^2*v^3 + 4*b*t^3*u + 6*b*t^2*u^2 + 12*b*t^2*u*v + 8*b*t*u^2*v + 12*b*t*u*v^2 + 2*b*u^2*v^2 + 4*b*u*v^3 + 4*t^3*u^2 + 10*t^2*u^2*v + 8*t*u^2*v^2 + 2*u^2*v^3 + t^2*u^2*w := by
    positivity
  have key : (-a^3*b^2*t^2 - 2*a^3*b*r*t^2 - a^3*r^2*t^2 + 2*a^2*b^2*r^2 + 4*a^2*b^2*r*t + 3*a^2*b^2*t^2 + 4*a^2*b*r^3 + 6*a^2*b*r^2*t + 4*a^2*b*r*t^2 + 2*a^2*r^4 + 2*a^2*r^3*t + a^2*r^2*t^2 - 4*a*b^2*r*t - 3*a*b^2*t^2 - 4*a*b*r^2*t - 2*a*b*r*t^2 + b^2*t^2) * (b+r)^3
      = (b+r)^2 * (2*b^3*t^2 + 4*b^3*t*v + 2*b^3*v^2 + 8*b^2*t^2*u + 2*b^2*t^2*v + 12*b^2*t*u*v + 4*b^2*t*v^2 + 4*b^2*u*v^2 + 2*b^2*v^3 + 4*b*t^3*u + 6*b*t^2*u^2 + 12*b*t^2*u*v + 8*b*t*u^2*v + 12*b*t*u*v^2 + 2*b*u^2*v^2 + 4*b*u*v^3 + 4*t^3*u^2 + 10*t^2*u^2*v + 8*t*u^2*v^2 + 2*u^2*v^3 + t^2*u^2*w) := by
    rw [hw, hu, hv]; ring
  have h3 : 0 < (b + r) ^ 3 := by positivity
  have h2 : 0 < (b + r) ^ 2 * (2*b^3*t^2 + 4*b^3*t*v + 2*b^3*v^2 + 8*b^2*t^2*u + 2*b^2*t^2*v + 12*b^2*t*u*v + 4*b^2*t*v^2 + 4*b^2*u*v^2 + 2*b^2*v^3 + 4*b*t^3*u + 6*b*t^2*u^2 + 12*b*t^2*u*v + 8*b*t*u^2*v + 12*b*t*u*v^2 + 2*b*u^2*v^2 + 4*b*u*v^3 + 4*t^3*u^2 + 10*t^2*u^2*v + 8*t*u^2*v^2 + 2*u^2*v^3 + t^2*u^2*w) := by
    positivity
  rw [← key] at h2
  exact pos_of_mul_pos_left h2 h3.le


set_option maxHeartbeats 1000000 in
theorem solution (prm : Params) (hs : Standing prm)
    (ha : A2 prm ≤ prm.alpha) :
    (∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (C0 prm) →
      b ∈ Set.Icc (0 : ℝ) (C0 prm) → a < b →
      profAstar prm b - profB1 prm b < profAstar prm a - profB1 prm a) ∧
    0 < profAstar prm 0 - profB1 prm 0 ∧
    profAstar prm (CA1 prm) - profB1 prm (CA1 prm) < 0 ∧
    CA1 prm < C0 prm := by
  obtain ⟨a, b, r, t, g⟩ := prm
  obtain ⟨⟨ha0, hb0, ht0, htr, hg0⟩, hbr, haA⟩ := hs
  dsimp only at ha0 hb0 ht0 htr hg0 hbr
  simp only [Acon] at haA
  simp only [A2] at ha
  have hr0 : 0 < r := lt_trans ht0 htr
  have hX : 0 < r * (r + b) + b * t := by positivity
  have hK0 : a ^ 2 * (r * (r + b) + b * t) < b * (r + t) := by
    have := (Real.lt_sqrt ha0.le).mp haA
    rwa [lt_div_iff₀ hX] at this
  have ha1 : a < 1 := by
    by_contra hcon
    push Not at hcon
    have : 1 ≤ a ^ 2 := by nlinarith
    nlinarith
  have hA2 : b ≤ a * (b + r) := by
    rwa [div_le_iff₀ (by linarith)] at ha
  have h1a : 0 < 1 - a := by linarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by nlinarith
  have hR1 : 0 < r + t * (1 - a) := by nlinarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have pE : 0 < r + t + a * (r - t) + b * (1 + a) := by nlinarith
  set P : Params := ⟨a, b, r, t, g⟩ with hP
  -- breakpoints
  have hW : 0 < 2*a*b*r+a*b*t+2*a*r^2+a*r*t-b*t := by
    have := mul_le_mul_of_nonneg_right hA2 (show (0:ℝ) ≤ 2*r+t by linarith)
    nlinarith
  have hCA1pos : 0 < CA1 P := by
    simp only [hP, CA1]
    apply div_pos
    · apply mul_pos hg0
      nlinarith [mul_pos ht0 hb0, mul_pos (mul_pos ht0 hb0) ha0]
    · exact mul_pos (mul_pos ha0 h1a) hR1
  have hCA12 : CA1 P < CA2 P := by
    have e := hi_ord12 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
    have : 0 < g*t*(-(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t))/(a*(1-a)*(r+t)*(r+t*(1-a))) := by
      apply div_pos
      · have : 0 < -(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t) := by linarith
        positivity
      · exact mul_pos (mul_pos (mul_pos ha0 h1a) hrt0) hR1
    linarith
  have hCA2C0 : CA2 P < C0 P := by
    have e := hi_ord20 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
    have : 0 < g*r*t/((1-a)*(r+t)) := div_pos (by positivity) (mul_pos h1a hrt0)
    linarith
  -- endpoint slopes
  have hF1 : (a-1)*(2*a*b*r+a*b*t+2*a*r^2+a*r*t-b*t)/(2*a*(r+b)*(r+t*(1-a))) < 0 := by
    apply div_neg_of_neg_of_pos
    · nlinarith
    · have : 0 < r + b := by linarith
      exact mul_pos (mul_pos (mul_pos two_pos ha0) this) hR1
  have hF2 : (2*a*(b+r)*(r+t) - 2*(b+r)*(r+t) + r*t)/(2*(r+b)*(r+t)) < 0 := by
    apply div_neg_of_neg_of_pos
    · have hY : (1 - a^2) * (r^2+r*b+b*t) > r^2 := by nlinarith
      have h2 : 2*(1-a) ≥ 1 - a^2 := by nlinarith [sq_nonneg (1-a)]
      have hZ : 0 < r^2+r*b+b*t := by positivity
      have h3 : r*(b+r)*(r+t) ≥ t*(r^2+r*b+b*t) := by
        nlinarith [mul_pos hb0 (mul_pos (sub_pos.mpr htr) (add_pos hr0 ht0))]
      have h4 : (1 - a^2) * (b+r)*(r+t) > r*t := by
        by_contra hc
        push Not at hc
        have : (1 - a^2) * (r^2+r*b+b*t) * ((b+r)*(r+t)) ≤ r*t*(r^2+r*b+b*t) := by
          have := mul_le_mul_of_nonneg_right hc hZ.le
          nlinarith
        nlinarith [mul_pos hbr0 hrt0]
      have h5 : 2*(1-a)*(b+r)*(r+t) ≥ (1 - a^2) * (b+r)*(r+t) := by
        have := mul_le_mul_of_nonneg_right h2 (mul_pos hbr0 hrt0).le
        nlinarith
      nlinarith
    · positivity
  have e1lo : 2 * (-(1-a)^2*(2*a*b+2*a*r+b+r+t)/(4*g*(r+b)*(r + t + a * (r - t) + b * (1 + a)))) * 0
      + (-(1-a)*(b+r+t)/(2*(r + t + a * (r - t) + b * (1 + a)))) < 0 := by
    rw [mul_zero, zero_add]
    apply div_neg_of_neg_of_pos
    · nlinarith
    · exact mul_pos two_pos pE
  have S1 := quad_piece _ _ _ _ _ (hi_G1 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0) e1lo
    (by rw [hi_e1hi a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0]; exact hF1)
  have S2 := quad_piece _ _ _ _ _ (hi_G2 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0)
    (by rw [hi_e2lo a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0]; exact hF1)
    (by rw [hi_e2hi a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0]; exact hF2)
  have S3 := quad_piece _ _ _ _ _ (hi_G3 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0)
    (by rw [hi_e3lo a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0]; exact hF2)
    (by rw [hi_e3hi a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0]; linarith)
  have cont1 := hi_cont1 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
  have cont2 := hi_cont2 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
  -- transfer to D
  set D : ℝ → ℝ := fun c => profAstar P c - profB1 P c with hD
  have T1 : StrictAntiOn D (Set.Icc 0 (CA1 P)) := by
    refine S1.congr ?_
    intro c hc
    simp only [hD]
    unfold profAstar
    rw [if_pos hc.2]
  have T2 : StrictAntiOn D (Set.Icc (CA1 P) (CA2 P)) := by
    refine S2.congr ?_
    intro c hc
    simp only [hD]
    unfold profAstar
    rcases eq_or_lt_of_le hc.1 with h1 | h1
    · rw [← h1, if_pos le_rfl, cont1]
    · rw [if_neg (not_le.mpr h1)]
      rcases eq_or_lt_of_le hc.2 with h2 | h2
      · rw [h2, if_neg (lt_irrefl _), cont2]
      · rw [if_pos h2]
  have T3 : StrictAntiOn D (Set.Icc (CA2 P) (C0 P)) := by
    refine S3.congr ?_
    intro c hc
    simp only [hD]
    unfold profAstar
    rw [if_neg (not_le.mpr (lt_of_lt_of_le hCA12 hc.1)), if_neg (not_lt.mpr hc.1)]
  have T12 : StrictAntiOn D (Set.Icc 0 (CA2 P)) := by
    have := T1.union T2 (isGreatest_Icc hCA1pos.le) (isLeast_Icc hCA12.le)
    rwa [Set.Icc_union_Icc_eq_Icc hCA1pos.le hCA12.le] at this
  have T : StrictAntiOn D (Set.Icc 0 (C0 P)) := by
    have hle : (0:ℝ) ≤ CA2 P := (hCA1pos.trans hCA12).le
    have := T12.union T3 (isGreatest_Icc hle) (isLeast_Icc hCA2C0.le)
    rwa [Set.Icc_union_Icc_eq_Icc hle hCA2C0.le] at this
  refine ⟨fun x y hx hy hxy => T hx hy hxy, ?_, ?_, ?_⟩
  · have e := hi_val0 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
    have hA : profAstar P 0 = profA1 P 0 := by
      unfold profAstar
      rw [if_pos hCA1pos.le]
    rw [hA, e]
    apply div_pos
    · have : 0 < b + r - t := by linarith
      positivity
    · exact mul_pos four_pos pE
  · have e := hi_valCA1 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
    have hA : profAstar P (CA1 P) = profA1 P (CA1 P) := by
      unfold profAstar
      rw [if_pos le_rfl]
    rw [hA, e]
    -- positivity of the numerator via the substitution u = a(b+r) - b, v = r - t
    have hN := hi_N_pos a b r t hb0 ht0 htr ha1 hA2
    apply div_neg_of_neg_of_pos
    · have := mul_pos hg0 hN
      linarith
    · have : 0 < r + b := by linarith
      have := mul_pos (mul_pos (mul_pos four_pos (pow_pos ha0 2)) this) (pow_pos hR1 2)
      exact this
  · have e := hi_ord10 a b r t g ha0 hb0 ht0 htr hg0 hbr ha1 hK0
    have : 0 < g*t*(a*b+a*r+b)/(a*(r+t*(1-a))) := div_pos (by positivity) (mul_pos ha0 hR1)
    linarith
