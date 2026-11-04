-- Prove2me | solution 1 for SolarNonOwn.BizChoice.crossing_low_alpha
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T11:27:37.019933+00:00
-- url     : https://prove2.me/submissions/602bb937-bdf3-4180-beed-8d4653bb4561

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

private lemma lo_G1 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    ∀ x y : ℝ, (profA1 (⟨a, b, r, t, g⟩ : Params) y - profB2 (⟨a, b, r, t, g⟩ : Params) y) - (profA1 (⟨a, b, r, t, g⟩ : Params) x - profB2 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * ((-(a-1)*(a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) * (x + y) + (-(-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a))))) := by
  intro x y
  simp only [profA1, profB2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_G2 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    ∀ x y : ℝ, (profA2 (⟨a, b, r, t, g⟩ : Params) y - profB2 (⟨a, b, r, t, g⟩ : Params) y) - (profA2 (⟨a, b, r, t, g⟩ : Params) x - profB2 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * ((-(a-1)^2*(a^4*b^2*r + a^4*b^2*t + 2*a^4*b*r^2 + 2*a^4*b*r*t + a^4*r^3 + a^4*r^2*t - 2*a^2*b^2*r - 2*a^2*b^2*t - 3*a^2*b*r^2 - 2*a^2*b*r*t + b^2*r + b^2*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * (x + y) + (-b*r*(a-1)*(a^2*b*t + a^2*r*t - b*r - b*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2))))) := by
  intro x y
  simp only [profA2, denomA2, profB2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_G3 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    ∀ x y : ℝ, (profA3 (⟨a, b, r, t, g⟩ : Params) y - profB2 (⟨a, b, r, t, g⟩ : Params) y) - (profA3 (⟨a, b, r, t, g⟩ : Params) x - profB2 (⟨a, b, r, t, g⟩ : Params) x) = (y - x) * ((b*(a-1)^2/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) * (x + y) + ((a-1)*(a^2*(b+r)^2 - b*r)/(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) := by
  intro x y
  simp only [profA3, profB2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_e12 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    2 * (-(a-1)^2*(a^4*b^2*r + a^4*b^2*t + 2*a^4*b*r^2 + 2*a^4*b*r*t + a^4*r^3 + a^4*r^2*t - 2*a^2*b^2*r - 2*a^2*b^2*t - 3*a^2*b*r^2 - 2*a^2*b*r*t + b^2*r + b^2*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * CA1 (⟨a, b, r, t, g⟩ : Params) + (-b*r*(a-1)*(a^2*b*t + a^2*r*t - b*r - b*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) = 2 * (-(a-1)*(a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) * CA1 (⟨a, b, r, t, g⟩ : Params) + (-(-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) := by
  simp only [CA1]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_e2hi (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    2 * (-(a-1)^2*(a^4*b^2*r + a^4*b^2*t + 2*a^4*b*r^2 + 2*a^4*b*r*t + a^4*r^3 + a^4*r^2*t - 2*a^2*b^2*r - 2*a^2*b^2*t - 3*a^2*b*r^2 - 2*a^2*b*r*t + b^2*r + b^2*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) * CA2 (⟨a, b, r, t, g⟩ : Params) + (-b*r*(a-1)*(a^2*b*t + a^2*r*t - b*r - b*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) = ((a-1)*(a^2*(b+r)^2*(r+t) - b*(b*r+b*t+2*r^2+r*t))/((r+t)*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) := by
  simp only [CA2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_e3lo (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    2 * (b*(a-1)^2/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) * CA2 (⟨a, b, r, t, g⟩ : Params) + ((a-1)*(a^2*(b+r)^2 - b*r)/(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))) = ((a-1)*(a^2*(b+r)^2*(r+t) - b*(b*r+b*t+2*r^2+r*t))/((r+t)*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) := by
  simp only [CA2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_e3hi (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    2 * (b*(a-1)^2/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) * C0 (⟨a, b, r, t, g⟩ : Params) + ((a-1)*(a^2*(b+r)^2 - b*r)/(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))) = a - 1 := by
  simp only [C0]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_val0A1 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    profA1 (⟨a, b, r, t, g⟩ : Params) 0 - profB2 (⟨a, b, r, t, g⟩ : Params) 0 = -g*(b+r)^2*(a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*t-b*r+b*t)/(2*(a-1)*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a))) := by
  simp only [profA1, profB2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_val0A2 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    profA2 (⟨a, b, r, t, g⟩ : Params) 0 - profB2 (⟨a, b, r, t, g⟩ : Params) 0 = b^2*g*r^2*(b+r-t)/(2*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2))) := by
  simp only [profA2, denomA2, profB2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_valCA2 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    profA3 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) - profB2 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) = -g*(a^2*b^3*r^2 + 2*a^2*b^3*r*t + a^2*b^3*t^2 + 3*a^2*b^2*r^3 + 5*a^2*b^2*r^2*t + 2*a^2*b^2*r*t^2 + 3*a^2*b*r^4 + 4*a^2*b*r^3*t + a^2*b*r^2*t^2 + a^2*r^5 + a^2*r^4*t - b^3*r^2 - 2*b^3*r*t - b^3*t^2 - 3*b^2*r^3 - 5*b^2*r^2*t - 2*b^2*r*t^2 - 2*b*r^4 - 2*b*r^3*t - b*r^2*t^2)/(2*(r+t)^2*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))) := by
  simp only [profA3, profB2, CA2]
  try rw [show b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 = -(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) by ring]
  generalize hBdef : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) = Bv at nB ⊢
  generalize hKdef : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) = Kv at nK ⊢
  generalize hEdef : r + t + a * (r - t) + b * (1 + a) = Ev at nE ⊢
  field_simp
  subst hBdef hKdef hEdef
  ring

private lemma lo_cont1 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    profA1 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) = profA2 (⟨a, b, r, t, g⟩ : Params) (CA1 (⟨a, b, r, t, g⟩ : Params)) := by
  simp only [profA1, profA2, denomA2, CA1]
  field_simp
  ring

private lemma lo_cont2 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    profA2 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) = profA3 (⟨a, b, r, t, g⟩ : Params) (CA2 (⟨a, b, r, t, g⟩ : Params)) := by
  simp only [profA2, profA3, denomA2, CA2]
  field_simp
  ring

private lemma lo_ord12 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    CA2 (⟨a, b, r, t, g⟩ : Params) - CA1 (⟨a, b, r, t, g⟩ : Params) = g*t*(-(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t))/(a*(1-a)*(r+t)*(r+t*(1-a))) := by
  simp only [CA1, CA2]
  field_simp
  ring

private lemma lo_ord20 (a b r t g : ℝ) (nE : r + t + a * (r - t) + b * (1 + a) ≠ 0) (nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0) (nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0) (nR1 : r + t * (1 - a) ≠ 0) (nR2 : r + t - a * t ≠ 0) (n1a : 1 - a ≠ 0) (na1 : a - 1 ≠ 0) (ng : g ≠ 0) (nrb : r + b ≠ 0) (nbr : b + r ≠ 0) (nrt : r + t ≠ 0) (na : a ≠ 0) (nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0) (nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0) :
    C0 (⟨a, b, r, t, g⟩ : Params) - CA2 (⟨a, b, r, t, g⟩ : Params) = g*r*t/((1-a)*(r+t)) := by
  simp only [C0, CA2]
  field_simp
  ring

private lemma lo_cert_F (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) (hbr' : b < r) :
    0 < (a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t) := by
  have hr0 : 0 < r := by linarith
  have hbr : 0 < b + r := by linarith
  have hq : 0 < a * (b + r) := by positivity
  have hsq : a ^ 2 * (b + r) ^ 2 < b ^ 2 := by nlinarith
  have hc : 0 < 2*b^2+3*b*r := by positivity
  have h1 : a^2*(2*b^2+3*b*r)*(b+r)^2 < b^2*(2*b^2+3*b*r) := by
    have := mul_lt_mul_of_pos_right hsq hc
    linarith
  have hb3 : b^3 ≤ 3*b*r^2 + r^3 := by
    have : b^2 < r^2 := by nlinarith
    nlinarith [mul_pos hb0 hr0, pow_pos hr0 3]
  have h2 : b^2*(2*b^2+3*b*r) ≤ b*(b+r)*(b+r)^2 := by
    have : b*(b^3) ≤ b*(3*b*r^2 + r^3) := mul_le_mul_of_nonneg_left hb3 hb0.le
    nlinarith
  have h3 : a^2*(2*b^2+3*b*r) < b*(b+r) := by
    have h4 : a^2*(2*b^2+3*b*r)*(b+r)^2 < b*(b+r)*(b+r)^2 := lt_of_lt_of_le h1 h2
    exact lt_of_mul_lt_mul_right h4 (by positivity)
  have key : (a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t) = a^4*(b+r)^2 + b*t*(1-a)^2 + (b^2+b*r - a^2*(2*b^2+3*b*r)) := by ring
  rw [key]
  have : 0 < b^2+b*r - a^2*(2*b^2+3*b*r) := by linarith
  positivity

private lemma lo_cert_Wp (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) :
    (a^2*b^3*r^2 + 2*a^2*b^3*r*t + a^2*b^3*t^2 + 3*a^2*b^2*r^3 + 5*a^2*b^2*r^2*t + 2*a^2*b^2*r*t^2 + 3*a^2*b*r^4 + 4*a^2*b*r^3*t + a^2*b*r^2*t^2 + a^2*r^5 + a^2*r^4*t - b^3*r^2 - 2*b^3*r*t - b^3*t^2 - 3*b^2*r^3 - 5*b^2*r^2*t - 2*b^2*r*t^2 - 2*b*r^4 - 2*b*r^3*t - b*r^2*t^2) < 0 := by
  have hr0 : 0 < r := by linarith
  have hq : 0 < a * (b + r) := by positivity
  have hsq : a ^ 2 * (b + r) ^ 2 - b ^ 2 < 0 := by nlinarith
  have key : (a^2*b^3*r^2 + 2*a^2*b^3*r*t + a^2*b^3*t^2 + 3*a^2*b^2*r^3 + 5*a^2*b^2*r^2*t + 2*a^2*b^2*r*t^2 + 3*a^2*b*r^4 + 4*a^2*b*r^3*t + a^2*b*r^2*t^2 + a^2*r^5 + a^2*r^4*t - b^3*r^2 - 2*b^3*r*t - b^3*t^2 - 3*b^2*r^3 - 5*b^2*r^2*t - 2*b^2*r*t^2 - 2*b*r^4 - 2*b*r^3*t - b*r^2*t^2) = (a^2*(b+r)^2-b^2)*((r+t)*(b*r+b*t+r^2)) - b*r*(2*b*r^2+4*b*r*t+2*b*t^2+2*r^3+2*r^2*t+r*t^2) := by ring
  rw [key]
  have h1 : (a^2*(b+r)^2-b^2)*((r+t)*(b*r+b*t+r^2)) < 0 := mul_neg_of_neg_of_pos hsq (by positivity)
  have h2 : 0 < b*r*(2*b*r^2+4*b*r*t+2*b*t^2+2*r^3+2*r^2*t+r*t^2) := by positivity
  linarith

private lemma lo_cert_B (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) :
    (a^2*(b+r)^2-b^2-2*b*r) < 0 := by
  have hr0 : 0 < r := by linarith
  have hq : 0 < a * (b + r) := by positivity
  nlinarith [mul_pos hb0 hr0]

private lemma lo_cert_X (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) :
    (-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t) < 0 := by
  have hr0 : 0 < r := by linarith
  obtain ⟨u, hu⟩ : ∃ u, u = b - a * (b + r) := ⟨_, rfl⟩
  have hu0 : 0 < u := by rw [hu]; linarith
  have hub : 0 < b - u := by rw [hu]; have := mul_pos ha0 (show (0:ℝ) < b + r by linarith); linarith
  obtain ⟨p, hp⟩ : ∃ p, p = 2 * b - u := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q, q = b - u := ⟨_, rfl⟩
  have hp0 : 0 < p := by rw [hp]; linarith
  have hq0 : 0 < q := by rw [hq]; exact hub
  have key : (-(-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t)) * (b + r) ^ 2 = (b+r)*(b^2*r^2 + b*r^3 + b*r^2*t + b*r*u*p + r^2*u*p + r*t*u*p + t*u^2*q) := by
    rw [hp, hq, hu]; ring
  have hM : 0 < (b+r)*(b^2*r^2 + b*r^3 + b*r^2*t + b*r*u*p + r^2*u*p + r*t*u*p + t*u^2*q) := by
    positivity
  rw [← key] at hM
  have := pos_of_mul_pos_left hM (by positivity)
  linarith

set_option maxHeartbeats 2000000 in
private lemma lo_cert_T (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) :
    (a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*t-b*r+b*t) < 0 := by
  obtain ⟨q, hq⟩ : ∃ q, q = a * (b + r) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = b - a * (b + r) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = r - t := ⟨_, rfl⟩
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hw0 : 0 < w := by rw [hw]; linarith
  have hv0 : 0 < v := by rw [hv]; linarith
  have key : (-(a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*t-b*r+b*t)) * (b + r) ^ 2 = q^2*t^2 + 2*q^2*t*v + 2*q^2*t*w + q^2*v^2 + 2*q^2*v*w + q*t^2*v + 2*q*t^2*w + 2*q*t*v^2 + 6*q*t*v*w + 2*q*t*w^2 + q*v^3 + 4*q*v^2*w + 3*q*v*w^2 + t^2*v*w + 2*t*v^2*w + 2*t*v*w^2 + v^3*w + 2*v^2*w^2 + v*w^3 := by
    subst hq hw hv; ring
  have hM : 0 < q^2*t^2 + 2*q^2*t*v + 2*q^2*t*w + q^2*v^2 + 2*q^2*v*w + q*t^2*v + 2*q*t^2*w + 2*q*t*v^2 + 6*q*t*v*w + 2*q*t*w^2 + q*v^3 + 4*q*v^2*w + 3*q*v*w^2 + t^2*v*w + 2*t*v^2*w + 2*t*v*w^2 + v^3*w + 2*v^2*w^2 + v*w^3 := by positivity
  have hp : 0 < (b + r) ^ 2 := by positivity
  rw [← key] at hM
  have := pos_of_mul_pos_left hM hp.le
  linarith

set_option maxHeartbeats 2000000 in
private lemma lo_cert_V (a b r t : ℝ) (ha0 : 0 < a) (hb0 : 0 < b) (ht0 : 0 < t) (htr : t < r) (hlow : a * (b + r) < b) :
    (a^2*(b+r)^2*(r+t) - b*(b*r+b*t+2*r^2+r*t)) < 0 := by
  obtain ⟨q, hq⟩ : ∃ q, q = a * (b + r) := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ : ∃ w, w = b - a * (b + r) := ⟨_, rfl⟩
  obtain ⟨v, hv⟩ : ∃ v, v = r - t := ⟨_, rfl⟩
  have hr0 : 0 < r := by linarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hw0 : 0 < w := by rw [hw]; linarith
  have hv0 : 0 < v := by rw [hv]; linarith
  have key : (-(a^2*(b+r)^2*(r+t) - b*(b*r+b*t+2*r^2+r*t))) * (b + r) ^ 2 = 3*q^3*t^2 + 5*q^3*t*v + 4*q^3*t*w + 2*q^3*v^2 + 2*q^3*v*w + 6*q^2*t^3 + 16*q^2*t^2*v + 17*q^2*t^2*w + 14*q^2*t*v^2 + 27*q^2*t*v*w + 10*q^2*t*w^2 + 4*q^2*v^3 + 10*q^2*v^2*w + 5*q^2*v*w^2 + 3*q*t^4 + 11*q*t^3*v + 16*q*t^3*w + 15*q*t^2*v^2 + 42*q*t^2*v*w + 21*q*t^2*w^2 + 9*q*t*v^3 + 36*q*t*v^2*w + 33*q*t*v*w^2 + 8*q*t*w^3 + 2*q*v^4 + 10*q*v^3*w + 12*q*v^2*w^2 + 4*q*v*w^3 + 3*t^4*w + 11*t^3*v*w + 8*t^3*w^2 + 15*t^2*v^2*w + 21*t^2*v*w^2 + 7*t^2*w^3 + 9*t*v^3*w + 18*t*v^2*w^2 + 11*t*v*w^3 + 2*t*w^4 + 2*v^4*w + 5*v^3*w^2 + 4*v^2*w^3 + v*w^4 := by
    subst hq hw hv; ring
  have hM : 0 < 3*q^3*t^2 + 5*q^3*t*v + 4*q^3*t*w + 2*q^3*v^2 + 2*q^3*v*w + 6*q^2*t^3 + 16*q^2*t^2*v + 17*q^2*t^2*w + 14*q^2*t*v^2 + 27*q^2*t*v*w + 10*q^2*t*w^2 + 4*q^2*v^3 + 10*q^2*v^2*w + 5*q^2*v*w^2 + 3*q*t^4 + 11*q*t^3*v + 16*q*t^3*w + 15*q*t^2*v^2 + 42*q*t^2*v*w + 21*q*t^2*w^2 + 9*q*t*v^3 + 36*q*t*v^2*w + 33*q*t*v*w^2 + 8*q*t*w^3 + 2*q*v^4 + 10*q*v^3*w + 12*q*v^2*w^2 + 4*q*v*w^3 + 3*t^4*w + 11*t^3*v*w + 8*t^3*w^2 + 15*t^2*v^2*w + 21*t^2*v*w^2 + 7*t^2*w^3 + 9*t*v^3*w + 18*t*v^2*w^2 + 11*t*v*w^3 + 2*t*w^4 + 2*v^4*w + 5*v^3*w^2 + 4*v^2*w^3 + v*w^4 := by positivity
  have hp : 0 < (b + r) ^ 2 := by positivity
  rw [← key] at hM
  have := pos_of_mul_pos_left hM hp.le
  linarith


set_option maxHeartbeats 1000000 in
theorem solution (prm : Params) (hs : Standing prm)
    (ha : prm.alpha < A2 prm) :
    (∀ a b : ℝ, a ∈ Set.Icc (0 : ℝ) (C0 prm) →
      b ∈ Set.Icc (0 : ℝ) (C0 prm) → a < b →
      profAstar prm b - profB2 prm b < profAstar prm a - profB2 prm a) ∧
    0 < profAstar prm 0 - profB2 prm 0 ∧
    profAstar prm (CA2 prm) - profB2 prm (CA2 prm) < 0 := by
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
  have hlow : a * (b + r) < b := by
    rwa [lt_div_iff₀ (by linarith)] at ha
  have h1a : 0 < 1 - a := by linarith
  have hK : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t < 0 := by linarith
  have pK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) < 0 := by linarith
  have hR1 : 0 < r + t * (1 - a) := by have := mul_pos ht0 h1a; linarith
  have hbr0 : 0 < b + r := by linarith
  have hrt0 : 0 < r + t := by linarith
  have pE : 0 < r + t + a * (r - t) + b * (1 + a) := by
    have := mul_pos ha0 (sub_pos.mpr htr); have := mul_pos hb0 ha0; linarith
  have hB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) < 0 := by
    have := lo_cert_B a b r t ha0 hb0 ht0 htr hlow
    linarith
  have hXc := lo_cert_X a b r t ha0 hb0 ht0 htr hlow
  have hFc := lo_cert_F a b r t ha0 hb0 ht0 htr hlow hbr
  have hTc := lo_cert_T a b r t ha0 hb0 ht0 htr hlow
  have hVc := lo_cert_V a b r t ha0 hb0 ht0 htr hlow
  have hWc := lo_cert_Wp a b r t ha0 hb0 ht0 htr hlow
  have nE : r + t + a * (r - t) + b * (1 + a) ≠ 0 := pE.ne'
  have nK : r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := pK.ne
  have nK2 : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) ≠ 0 := by
    have : a ^ 2 * r ^ 2 - b * (r + t) * (1 - a ^ 2) < 0 := by linarith
    exact this.ne
  have nK' : a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t ≠ 0 := hK.ne
  have nR1 : r + t * (1 - a) ≠ 0 := hR1.ne'
  have nR2 : r + t - a * t ≠ 0 := by
    have : a * t < t := mul_lt_of_lt_one_left ht0 ha1
    have : 0 < r + t - a * t := by linarith
    exact this.ne'
  have n1a : 1 - a ≠ 0 := h1a.ne'
  have na1 : a - 1 ≠ 0 := by linarith
  have ng : g ≠ 0 := hg0.ne'
  have nrb : r + b ≠ 0 := by linarith
  have nbr : b + r ≠ 0 := by linarith
  have nrt : r + t ≠ 0 := by linarith
  have na : a ≠ 0 := ha0.ne'
  have nB : a ^ 2 * (r + b) ^ 2 - b * (2 * r + b) ≠ 0 := hB.ne
  have nB2 : b * (2 * r + b) - a ^ 2 * (r + b) ^ 2 ≠ 0 := by linarith
  set P : Params := ⟨a, b, r, t, g⟩ with hP
  have hCA12 : CA1 P < CA2 P := by
    have e := lo_ord12 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
    have : 0 < g*t*(-(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t))/(a*(1-a)*(r+t)*(r+t*(1-a))) := by
      apply div_pos
      · have : 0 < -(a^2*b*r+a^2*b*t+a^2*r^2-b*r-b*t) := by linarith
        positivity
      · exact mul_pos (mul_pos (mul_pos ha0 h1a) hrt0) hR1
    linarith
  have hCA2C0 : CA2 P < C0 P := by
    have e := lo_ord20 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
    have : 0 < g*r*t/((1-a)*(r+t)) := div_pos (by positivity) (mul_pos h1a hrt0)
    linarith
  have hCA2pos : 0 < CA2 P := by
    simp only [hP, CA2]
    exact div_pos (by positivity) (mul_pos h1a hrt0)
  have cont1 := lo_cont1 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
  have cont2 := lo_cont2 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
  -- slope signs
  have hBE : (a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) * (r + t + a * (r - t) + b * (1 + a)) < 0 :=
    mul_neg_of_neg_of_pos hB pE
  have hBK : 0 < (a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) * (r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)) :=
    mul_pos_of_neg_of_neg hB pK
  have k1_1neg : (-(-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) < 0 :=
    div_neg_of_pos_of_neg (by linarith) hBE
  have k2_1neg : (-(a-1)*(a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) < 0 := by
    apply div_neg_of_pos_of_neg
    · have : 0 < -(a-1) := by linarith
      exact mul_pos this hFc
    · have := mul_neg_of_pos_of_neg (mul_pos two_pos hg0) hBE
      linarith
  have hZ : a^2*b*t + a^2*r*t - b*r - b*t < 0 := by
    have h1 : a * (a * (b + r)) < a * b := mul_lt_mul_of_pos_left hlow ha0
    have h2 : a * b < b := mul_lt_of_lt_one_left hb0 ha1
    have h3 : t * (a * (a * (b + r))) < t * b := mul_lt_mul_of_pos_left (by linarith) ht0
    have h4 : 0 < b * r := mul_pos hb0 hr0
    linarith
  have k1_2neg : (-b*r*(a-1)*(a^2*b*t + a^2*r*t - b*r - b*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r ^ 2 * a ^ 2 - b * (r + t) * (1 - a ^ 2)))) < 0 := by
    apply div_neg_of_neg_of_pos _ hBK
    have : 0 < (a-1)*(a^2*b*t + a^2*r*t - b*r - b*t) := mul_pos_of_neg_of_neg (by linarith) hZ
    have := mul_pos (mul_pos hb0 hr0) this
    linarith
  have hFv : ((a-1)*(a^2*(b+r)^2*(r+t) - b*(b*r+b*t+2*r^2+r*t))/((r+t)*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)))) < 0 :=
    div_neg_of_pos_of_neg (mul_pos_of_neg_of_neg (by linarith) hVc) (mul_neg_of_pos_of_neg hrt0 hB)
  have S3 := quad_piece _ _ _ _ _ (lo_G3 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2)
    (by rw [lo_e3lo a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2]; exact hFv)
    (by rw [lo_e3hi a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2]; linarith)
  set D : ℝ → ℝ := fun c => profAstar P c - profB2 P c with hD
  have T3 : StrictAntiOn D (Set.Icc (CA2 P) (C0 P)) := by
    refine S3.congr ?_
    intro c hc
    simp only [hD]
    unfold profAstar
    rw [if_neg (not_le.mpr (lt_of_lt_of_le hCA12 hc.1)), if_neg (not_lt.mpr hc.1)]
  have hDCA2 : D (CA2 P) < 0 := by
    have e := lo_valCA2 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
    have hA : profAstar P (CA2 P) = profA3 P (CA2 P) := by
      unfold profAstar
      rw [if_neg (not_le.mpr hCA12), if_neg (lt_irrefl _)]
    simp only [hD]
    rw [hA, e]
    apply div_neg_of_pos_of_neg
    · have := mul_pos hg0 (show 0 < -(a^2*b^3*r^2 + 2*a^2*b^3*r*t + a^2*b^3*t^2 + 3*a^2*b^2*r^3 + 5*a^2*b^2*r^2*t + 2*a^2*b^2*r*t^2 + 3*a^2*b*r^4 + 4*a^2*b*r^3*t + a^2*b*r^2*t^2 + a^2*r^5 + a^2*r^4*t - b^3*r^2 - 2*b^3*r*t - b^3*t^2 - 3*b^2*r^3 - 5*b^2*r^2*t - 2*b^2*r*t^2 - 2*b*r^4 - 2*b*r^3*t - b*r^2*t^2) by linarith)
      linarith
    · have := mul_pos two_pos (pow_pos hrt0 2)
      exact mul_neg_of_pos_of_neg this hB
  rcases lt_or_ge 0 (CA1 P) with hpos | hnp
  · -- three pieces
    have d1hi : 2 * (-(a-1)*(a^4*(b+r)^2 - 2*a^2*b^2 - 3*a^2*b*r + a^2*b*t - 2*a*b*t + b^2 + b*r + b*t)/(2*g*(a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) * CA1 P + (-(-a^3*b^2*t - 2*a^3*b*r*t - a^3*r^2*t + a^2*b^2*r + 2*a^2*b^2*t + 2*a^2*b*r^2 + 3*a^2*b*r*t + a^2*r^3 + a^2*r^2*t - a*b^2*t - b^2*r - b*r^2 - b*r*t)/((a ^ 2 * (r + b) ^ 2 - b * (2 * r + b))*(r + t + a * (r - t) + b * (1 + a)))) < 0 := by
      have := mul_neg_of_neg_of_pos k2_1neg hpos
      linarith
    have S1 := quad_piece _ _ _ _ _ (lo_G1 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2)
      (by rw [mul_zero, zero_add]; exact k1_1neg) d1hi
    have S2 := quad_piece _ _ _ _ _ (lo_G2 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2)
      (by rw [lo_e12 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2]; exact d1hi)
      (by rw [lo_e2hi a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2]; exact hFv)
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
    have T12 : StrictAntiOn D (Set.Icc 0 (CA2 P)) := by
      have := T1.union T2 (isGreatest_Icc hpos.le) (isLeast_Icc hCA12.le)
      rwa [Set.Icc_union_Icc_eq_Icc hpos.le hCA12.le] at this
    have T : StrictAntiOn D (Set.Icc 0 (C0 P)) := by
      have := T12.union T3 (isGreatest_Icc hCA2pos.le) (isLeast_Icc hCA2C0.le)
      rwa [Set.Icc_union_Icc_eq_Icc hCA2pos.le hCA2C0.le] at this
    refine ⟨fun x y hx hy hxy => T hx hy hxy, ?_, hDCA2⟩
    have e := lo_val0A1 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
    have hA : profAstar P 0 = profA1 P 0 := by
      unfold profAstar
      rw [if_pos hpos.le]
    rw [hA, e]
    apply div_pos
    · have := mul_pos hg0 (pow_pos hbr0 2)
      have := mul_pos this (show 0 < -(a^2*b*r+a^2*b*t+a^2*r^2-2*a*b*t-b*r+b*t) by linarith)
      linarith
    · have : 0 < (a - 1) * (a ^ 2 * (r + b) ^ 2 - b * (2 * r + b)) := mul_pos_of_neg_of_neg (by linarith) hB
      have := mul_pos (mul_pos two_pos this) pE
      linarith
  · -- two pieces
    have S2 := quad_piece _ _ _ _ _ (lo_G2 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2)
      (by rw [mul_zero, zero_add]; exact k1_2neg)
      (by rw [lo_e2hi a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2]; exact hFv)
    have T2 : StrictAntiOn D (Set.Icc 0 (CA2 P)) := by
      refine S2.congr ?_
      intro c hc
      simp only [hD]
      unfold profAstar
      by_cases h1 : c ≤ CA1 P
      · have hc1 : c = CA1 P := le_antisymm h1 (le_trans hnp hc.1)
        rw [if_pos h1, hc1, cont1]
      · rw [if_neg h1]
        rcases eq_or_lt_of_le hc.2 with h2 | h2
        · rw [h2, if_neg (lt_irrefl _), cont2]
        · rw [if_pos h2]
    have T : StrictAntiOn D (Set.Icc 0 (C0 P)) := by
      have := T2.union T3 (isGreatest_Icc hCA2pos.le) (isLeast_Icc hCA2C0.le)
      rwa [Set.Icc_union_Icc_eq_Icc hCA2pos.le hCA2C0.le] at this
    refine ⟨fun x y hx hy hxy => T hx hy hxy, ?_, hDCA2⟩
    have e := lo_val0A2 a b r t g nE nK nK2 nK' nR1 nR2 n1a na1 ng nrb nbr nrt na nB nB2
    have hA : profAstar P 0 = profA2 P 0 := by
      unfold profAstar
      by_cases h1 : (0:ℝ) ≤ CA1 P
      · have hc1 : (0:ℝ) = CA1 P := le_antisymm h1 hnp
        rw [if_pos h1, hc1, cont1]
      · rw [if_neg h1, if_pos hCA2pos]
    rw [hA, e]
    apply div_pos
    · have : 0 < b + r - t := by linarith
      positivity
    · rw [mul_assoc]; exact mul_pos two_pos hBK
