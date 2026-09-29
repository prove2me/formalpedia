-- Prove2me | solution 1 for WorkbookCorrected.base_54697
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T12:12:54.514985+00:00
-- url     : https://prove2.me/submissions/3c6c80a8-5942-48ef-a5fb-dc61ab692850

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (x : ℝ) (hx : 0 ≤ x) : 663*x^4 - 620*x^3 - 790*x^2 + 284*x + 503 > 0 := by
  have hid : 663*x^4 - 620*x^3 - 790*x^2 + 284*x + 503 = 663 * (x^2 - (310/663 : ℝ)*x - (777/1000 : ℝ))^2 + (31610113/331500 : ℝ) * (x + (-32775405/31610113 : ℝ))^2 + (6729059407049/31610113000000 : ℝ) := by ring
  rw [hid]
  positivity
example : (∀ (x : ℝ) (hx : 0 ≤ x), 663*x^4 - 620*x^3 - 790*x^2 + 284*x + 503 > 0) := @solution
#print axioms solution
