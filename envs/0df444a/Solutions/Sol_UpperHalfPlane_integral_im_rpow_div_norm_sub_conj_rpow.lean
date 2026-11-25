-- Prove2me | solution 1 for UpperHalfPlane.integral_im_rpow_div_norm_sub_conj_rpow
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-25T02:21:42.588958+00:00
-- url     : https://prove2.me/submissions/c94df783-6680-4c32-8b78-ea7ed6031462

import Mathlib
import Definitions.Def_RPLib_S3_Bergman

set_option autoImplicit false

theorem solution (w : UpperHalfPlane) (σ : ℝ) (hσ : 1 < σ) :
    MeasureTheory.Integrable
        (fun z : UpperHalfPlane => z.im ^ σ / ‖(z : ℂ) - starRingEnd ℂ (w : ℂ)‖ ^ (2 * σ)) ∧
      ∫ z : UpperHalfPlane, z.im ^ σ / ‖(z : ℂ) - starRingEnd ℂ (w : ℂ)‖ ^ (2 * σ) =
        4 * Real.pi / ((σ - 1) * (4 * w.im) ^ σ) := by
  exact ⟨RamanujanPetersson.Bergman.integrable_kernel w hσ, RamanujanPetersson.Bergman.integral_kernel w hσ⟩
