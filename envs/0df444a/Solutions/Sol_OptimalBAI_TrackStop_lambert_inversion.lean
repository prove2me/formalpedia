-- Prove2me | solution 1 for OptimalBAI.TrackStop.lambert_inversion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:50:36.385233+00:00
-- url     : https://prove2.me/submissions/12d6060b-6952-4883-a27d-1fe0ee4ae8dd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
set_option autoImplicit false

theorem solution (α : ℝ) (hα : α ∈ Set.Icc (1 : ℝ) (Real.exp 1 / 2))
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hy : c₁ ^ α < c₂)
    (x : ℝ)
    (hx : x = α / c₁ * (Real.log (c₂ * Real.exp 1 / c₁ ^ α) + Real.log (Real.log (c₂ / c₁ ^ α))))
    (hx_pos : 0 < x) :
    Real.log (c₂ * x ^ α) ≤ c₁ * x := by
  let y : ℝ := Real.log (c₂ / c₁ ^ α)
  have hp : 0 < c₁ ^ α := Real.rpow_pos_of_pos hc₁ α
  have hypos : 0 < y := Real.log_pos ((one_lt_div hp).mpr hy)
  have hapos : 0 < α := lt_of_lt_of_le zero_lt_one hα.1
  have hlog : Real.log (c₂ * Real.exp 1 / c₁ ^ α) = y+1 := by
    rw [show c₂ * Real.exp 1 / c₁ ^ α = (c₂ / c₁ ^ α) * Real.exp 1 by ring,
      Real.log_mul (div_ne_zero hc₂.ne' hp.ne') (Real.exp_ne_zero 1), Real.log_exp]
  have hcx : c₁*x = α*(y+1+Real.log y) := by
    rw [hx, hlog]
    dsimp [y]
    field_simp
  have hupper : c₁*x ≤ Real.exp 1 * y := by
    calc
      c₁*x = α*(y+1+Real.log y) := hcx
      _ ≤ α*(2*y) := mul_le_mul_of_nonneg_left (by linarith [Real.log_le_sub_one_of_pos hypos]) hapos.le
      _ = (2*α)*y := by ring
      _ ≤ Real.exp 1*y := mul_le_mul_of_nonneg_right (by linarith [hα.2]) hypos.le
  have hl : Real.log c₁ + Real.log x ≤ 1 + Real.log y := by
    have hh := Real.log_le_log (mul_pos hc₁ hx_pos) hupper
    simpa [Real.log_mul hc₁.ne' hx_pos.ne',
      Real.log_mul (Real.exp_ne_zero 1) hypos.ne', Real.log_exp] using hh
  have hyid : y = Real.log c₂ - α*Real.log c₁ := by
    dsimp [y]
    rw [Real.log_div hc₂.ne' hp.ne', Real.log_rpow hc₁]
  rw [Real.log_mul hc₂.ne' (Real.rpow_pos_of_pos hx_pos α).ne', Real.log_rpow hx_pos]
  have hm := mul_le_mul_of_nonneg_left hl hapos.le
  have hya : y ≤ α*y := by nlinarith [hα.1]
  nlinarith
