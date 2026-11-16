-- Prove2me | solution 1 for PHIP1887.critical_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:22:04.066282+00:00
-- url     : https://prove2.me/submissions/a249f16b-a8fb-497e-b938-d360c12732fa

import Mathlib

theorem solution (x b : ℝ) (hx : 0 < x) (hb : 0 < b) :
    0 < x/(x+b) ∧ x/(x+b) < 1 := by
  have hd : 0 < x+b := add_pos hx hb
  constructor
  · exact div_pos hx hd
  · exact (div_lt_one hd).mpr (by linarith)
