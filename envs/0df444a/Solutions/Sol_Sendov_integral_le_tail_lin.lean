-- Prove2me | solution 1 for Sendov.integral_le_tail_lin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T18:50:06.360196+00:00
-- url     : https://prove2.me/submissions/a1990c11-6b04-4d2a-a348-66f9184b3c08

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_integral_chord_lin
import Theorems.Thm_Sendov_integral_le_tail_gen

set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) :
    (∫ t in (0 : ℝ)..1, t * QQ c A t ^ r)
      ≤ 1 / (c ^ 2 * ((r + 1) * (r + 2))) + QQ c A 1 ^ r / 2 := by
  have h := integral_le_tail_gen hfeas hc hc1 hr 1
  simp only [pow_one] at h
  rw [integral_chord_lin hr hc, show ((1 : ℕ) : ℝ) + 1 = 2 by norm_num] at h
  exact h
end Sendov
