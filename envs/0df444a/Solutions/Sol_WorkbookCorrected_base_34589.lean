-- Prove2me | solution 1 for WorkbookCorrected.base_34589
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:50.300372+00:00
-- url     : https://prove2.me/submissions/4217aa93-de4d-4b81-8c54-bc6e13b08e66

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (source_domain_a : 0 ≤ a) (source_domain_b : 0 ≤ b) (source_domain_c : 0 ≤ c) (source_domain_d : 0 ≤ d) (h : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2 + 2) : a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 + 1 ≥ a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + d ^ 3 * a  := by
  have hw0 : 0 ≤ (2*a^4 - a^2*b^2 - a^2*d^2 + 2*b^4 - b^2*c^2 + 2*c^4 - c^2*d^2 + 2*d^4 - 2) := by linarith only [h]
  have hw1 : 0 ≤ (-2*a^4 + a^2*b^2 + a^2*d^2 - 2*b^4 + b^2*c^2 - 2*c^4 + c^2*d^2 - 2*d^4 + 2) := by linarith only [h]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (-a^2/2 - a*d/2 - c^2/2 + c*d/2 + d^2)^2 + (1 : ℝ) * (1) * (-a^2/2 + a*b/2 + b^2 - b*c/2 - c^2/2)^2 + (1/2 : ℝ) * (1) * (-a^2 + a*b/2 - a*d/2 + b*c/2 + c^2 - c*d/2)^2 + (1/8 : ℝ) * (1) * (a*b + a*d + b*c + c*d)^2 + (1/2 : ℝ) * ((-2*a^4 + a^2*b^2 + a^2*d^2 - 2*b^4 + b^2*c^2 - 2*c^4 + c^2*d^2 - 2*d^4 + 2)) * (1)^2 := by positivity
  have hid : ( a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 + 1 ) - ( a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + d ^ 3 * a  ) = (1 : ℝ) * (1) * (-a^2/2 - a*d/2 - c^2/2 + c*d/2 + d^2)^2 + (1 : ℝ) * (1) * (-a^2/2 + a*b/2 + b^2 - b*c/2 - c^2/2)^2 + (1/2 : ℝ) * (1) * (-a^2 + a*b/2 - a*d/2 + b*c/2 + c^2 - c*d/2)^2 + (1/8 : ℝ) * (1) * (a*b + a*d + b*c + c*d)^2 + (1/2 : ℝ) * ((-2*a^4 + a^2*b^2 + a^2*d^2 - 2*b^4 + b^2*c^2 - 2*c^4 + c^2*d^2 - 2*d^4 + 2)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (source_domain_a : 0 ≤ a) (source_domain_b : 0 ≤ b) (source_domain_c : 0 ≤ c) (source_domain_d : 0 ≤ d) (h : 2 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) = a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * d ^ 2 + d ^ 2 * a ^ 2 + 2), a * b ^ 3 + b * c ^ 3 + c * d ^ 3 + d * a ^ 3 + 1 ≥ a ^ 3 * b + b ^ 3 * c + c ^ 3 * d + d ^ 3 * a) := @solution
#print axioms solution
