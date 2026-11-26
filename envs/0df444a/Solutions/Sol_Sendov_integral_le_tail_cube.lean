-- Prove2me | solution 1 for Sendov.integral_le_tail_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:08:26.49646+00:00
-- url     : https://prove2.me/submissions/728fb999-ad28-45f6-8aff-5de4b92377b0

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_integral_chord_pow
import Theorems.Thm_Sendov_integral_le_tail_gen

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t ^ 3 * QQ c A t ^ r)
      ≤ 6 / (c ^ 4 * ((r + 1) * (r + 2) * (r + 3) * (r + 4))) + QQ c A 1 ^ r / 4 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 3
  rw [integral_chord_pow hr hc, show ((3 : ℕ) : ℝ) + 1 = 4 by norm_num] at h
  exact h
end Sendov
