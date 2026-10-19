-- Prove2me | solution 1 for ToddKK14.Diameter.log_swap
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-18T19:33:41.370283+00:00
-- url     : https://prove2.me/submissions/b74b6618-a018-472c-afc5-ee2993c7e441

import Mathlib

set_option autoImplicit false

theorem solution (d n : ℕ) (hd : 1 ≤ d) (hdn : d < n) :
    ((n : ℝ) - d) ^ Real.logb 2 d = (d : ℝ) ^ Real.logb 2 ((n : ℝ) - d) := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hnd : (0 : ℝ) < (n : ℝ) - d := by
    have : (d : ℝ) < n := by exact_mod_cast hdn
    linarith
  rw [Real.rpow_def_of_pos hnd, Real.rpow_def_of_pos hd']
  congr 1
  unfold Real.logb
  ring
