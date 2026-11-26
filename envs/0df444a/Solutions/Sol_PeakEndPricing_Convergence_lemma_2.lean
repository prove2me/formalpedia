-- Prove2me | solution 1 for PeakEndPricing.Convergence.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T21:55:49.659934+00:00
-- url     : https://prove2.me/submissions/3ebb888c-1eb1-414a-bfa8-f2f2bea16fec

import Mathlib
import Definitions.Def_PeakEndPricing_Convergence_Model
namespace PeakEndPricing.Convergence

theorem _root_.solution (pbar : ℝ) (d0 : ℝ → ℝ) (lam gam : ℝ) (hgam : 0 < gam) (hlam : gam ≤ lam) :
    (∀ p ∈ Set.Icc (0 : ℝ) pbar, ∀ r : ℝ,
      profit d0 lam gam p r = min (profitK d0 lam p r) (profitK d0 gam p r)) ∧
    SupermodularOn (profit d0 lam gam) (Set.Icc (0 : ℝ) pbar) (Set.Icc (0 : ℝ) pbar) := by
  have hk : ∀ p r k : ℝ, profitK d0 k p r = p * d0 p + k * (r - p) * p := fun _ _ _ => rfl
  have hp0 : ∀ p r : ℝ, profit d0 lam gam p r = p * (d0 p - lam * max (p - r) 0 + gam * max (r - p) 0) := fun _ _ => rfl
  constructor
  · intro p hp r
    have hp1 := hp.1
    rw [hp0, hk, hk]
    rcases le_total p r with h | h
    · rw [max_eq_right (by linarith : p - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - p), min_eq_right]
      · ring
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hlam) (sub_nonneg.2 h)) hp1]
    · rw [max_eq_left (by linarith : 0 ≤ p - r), max_eq_right (by linarith : r - p ≤ 0), min_eq_left]
      · ring
      · nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.2 hlam) (sub_nonneg.2 h)) hp1]
  · intro xl hxl xh hxh yl _ yh _ hx hy
    have hdl : 0 ≤ lam - gam := sub_nonneg.2 hlam
    have h0 := hxl.1
    have key : ∀ p r : ℝ, profit d0 lam gam p r = p * d0 p + gam * (p * (r - p)) - (lam - gam) * (p * max (p - r) 0) := by
      intro p r
      rw [hp0]
      have : max (r - p) 0 = max (p - r) 0 + (r - p) := by
        rcases le_total p r with h | h
        · rw [max_eq_right (by linarith : p - r ≤ 0), max_eq_left (by linarith : 0 ≤ r - p)]; ring
        · rw [max_eq_left (by linarith : 0 ≤ p - r), max_eq_right (by linarith : r - p ≤ 0)]; ring
      rw [this]; ring
    have m : xh * max (xh - yh) 0 - xl * max (xl - yh) 0 ≤ xh * max (xh - yl) 0 - xl * max (xl - yl) 0 := by
      rcases max_cases (xh - yh) 0 with ⟨a, _⟩ | ⟨a, _⟩ <;> rcases max_cases (xl - yh) 0 with ⟨b, _⟩ | ⟨b, _⟩ <;>
      rcases max_cases (xh - yl) 0 with ⟨c, _⟩ | ⟨c, _⟩ <;> rcases max_cases (xl - yl) 0 with ⟨d, _⟩ | ⟨d, _⟩ <;>
      rw [a, b, c, d] <;> nlinarith [mul_nonneg h0 (sub_nonneg.2 hy.le), mul_nonneg (sub_nonneg.2 hx.le) (sub_nonneg.2 hy.le)]
    have := mul_le_mul_of_nonneg_left m hdl
    have g := mul_nonneg hgam.le (mul_nonneg (sub_nonneg.2 hx.le) (sub_nonneg.2 hy.le))
    rw [key, key, key, key]
    nlinarith


end PeakEndPricing.Convergence

