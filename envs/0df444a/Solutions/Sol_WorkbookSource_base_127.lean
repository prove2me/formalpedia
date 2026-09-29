-- Prove2me | solution 1 for WorkbookSource.base_127
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:16:53.074085+00:00
-- url     : https://prove2.me/submissions/5a5a1136-fcb8-47f9-a2fa-7a1a7f85be4c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (x + y) * (y + z) * (z + x) / (4 * x * y * z) ≥ (x + z) / (y + z) + (y + z) / (x + z)  := by
  have hn : 0 ≤ (x^3*y^2 - 2*x^3*y*z + x^3*z^2 + x^2*y^3 + 4*x^2*y^2*z - 3*x^2*y*z^2 + 2*x^2*z^3 - 2*x*y^3*z - 3*x*y^2*z^2 - 4*x*y*z^3 + x*z^4 + y^3*z^2 + 2*y^2*z^3 + y*z^4) := by
    have hs0 : 0 ≤ (1 : ℝ) * (y) * (-x*y - x*z + y*z + z^2)^2 := by positivity
    have hs1 : 0 ≤ (1 : ℝ) * (x) * (-x*y + x*z - y*z + z^2)^2 := by positivity
    nlinarith only [hs0, hs1]
  have hd : 0 < (4*x*y*z*(x + z)*(y + z) : ℝ) := by positivity
  have he : ( (x + y) * (y + z) * (z + x) / (4 * x * y * z) ) - ( (x + z) / (y + z) + (y + z) / (x + z)  ) = (x^3*y^2 - 2*x^3*y*z + x^3*z^2 + x^2*y^3 + 4*x^2*y^2*z - 3*x^2*y*z^2 + 2*x^2*z^3 - 2*x*y^3*z - 3*x*y^2*z^2 - 4*x*y*z^3 + x*z^4 + y^3*z^2 + 2*y^2*z^3 + y*z^4) / (4*x*y*z*(x + z)*(y + z)) := by
    field_simp (disch := positivity)
    <;> ring
  have hp := div_nonneg hn (le_of_lt hd)
  rw [← he] at hp
  linarith only [hp]
example : (∀ (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z), (x + y) * (y + z) * (z + x) / (4 * x * y * z) ≥ (x + z) / (y + z) + (y + z) / (x + z)) := @solution
#print axioms solution
