-- Prove2me | solution 1 for WeilDefect.RPB108.energy_lower_of_form_blocks
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-11T04:58:40.49527+00:00
-- url     : https://prove2.me/submissions/a18b5dc1-a2c6-439e-b0b4-357426c76b26

import Theorems.Thm_WeilDefect_RPB108_high_form_square_completion
import Mathlib
import Definitions.Def_RPB108_ThreeGram
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
open WeilDefect.RPB108

namespace WeilDefect.RPB108
/-- Pay the real mixed cross by its complex norm, retaining the exact sign. -/
theorem complex_mixed_cross_lower (z w : ℂ) :
    -2*‖z‖*‖w‖ ≤ 2*(star z*w).re := by
  have hr := (abs_le.mp (Complex.abs_re_le_norm (star z*w))).1
  rw [norm_mul, norm_star] at hr
  linarith
end WeilDefect.RPB108

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (B : E → E → ℂ) (T : E →L[ℂ] E)
    (hleft : ∀ u v w, B (u-v) w = B u w-B v w)
    (hright : ∀ u v w, B u (v-w) = B u v-B u w)
    (hsym : ∀ u v, (B u v).re = (B v u).re)
    (R h : E) (hsolve : ∀ u, B (T R) u = inner ℂ R u)
    (N D V actualRetained A k energy : ℝ) (z p q : ℂ)
    (hraw : energy = N+2*(inner ℂ R (h-T R)).re+(B (h-T R) (h-T R)).re)
    (hfinite : N-(inner ℂ R (T R)).re =
      D*‖z‖^2+2*(star z*(p-q)).re+actualRetained)
    (hD : A ≤ D) (hretained : V ≤ actualRetained)
    (hhigh : k*‖h‖^2 ≤ (B h h).re) :
    A*‖z‖^2-2*‖z‖*‖p-q‖+V+k*‖h‖^2 ≤ energy := by
  have hc := high_form_square_completion B T hleft hright hsym R h hsolve
  have hx := complex_mixed_cross_lower z (p-q)
  have hd := mul_le_mul_of_nonneg_right hD (sq_nonneg ‖z‖)
  linarith
