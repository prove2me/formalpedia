-- Prove2me | solution 1 for ZudilinZeta.zudilin_numeric_C0_gt_C1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-10-01T17:12:30.959376+00:00
-- url     : https://prove2.me/submissions/8ee625e6-358e-4468-bed3-b82e837ddd09
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds
import Theorems.Thm_ZudilinZeta_zudilin_numeric_C1_bounds

set_option autoImplicit false

open ZudilinZeta

theorem solution (τ₀ : ℂ)
    (hroot : charPoly params13 τ₀ = 0) (him : 0 < τ₀.im)
    (hmax : ∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) :
    (227.58019641 ≤ C0 params13 τ₀ ∧ C0 params13 τ₀ < 227.58019642) ∧
      (226.24944266 ≤ C1 params13 ∧ C1 params13 < 226.24944267) ∧
      C1 params13 < C0 params13 τ₀ := by
  have h0 := zudilin_numeric_C0_bounds τ₀ hroot him hmax
  have h1 := zudilin_numeric_C1_bounds
  exact ⟨h0, h1, by linarith only [h0.1, h1.2]⟩
