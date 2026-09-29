-- Prove2me | solution 1 for WorkbookSource.base_45570
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:57:25.717377+00:00
-- url     : https://prove2.me/submissions/a431827a-894a-40be-b4a8-9cf581c0997c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (a b c : ℝ) : 2 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + a ^ 6 + b ^ 6 + c ^ 6 ≥ 0  := by
  have h0 : 0 ≤ (80/47 : ℝ) * (19*a^3/40 - 9*a^2*b/80 - 9*a^2*c/80 - 9*a*b^2/80 + a*b*c - 9*a*c^2/80 + 19*b^3/40 - 9*b^2*c/80 - 9*b*c^2/80 + 19*c^3/40)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (579/940 : ℝ) * (133*a^3/193 + 57*a^2*b/386 - 63*a^2*c/386 + 57*a*b^2/386 + 57*a*c^2/386 + 133*b^3/193 - 63*b^2*c/386 + 57*b*c^2/386 + c^3)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h2 : 0 ≤ (12627/36284 : ℝ) * (114*a^3/1403 + a^2*b + 745*a^2*c/1403 + 631*a*b^2/1403 + 631*a*c^2/1403 - 658*b^3/1403 + 745*b^2*c/1403 + b*c^2)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h3 : 0 ≤ (21177/65941 : ℝ) * (a^3 + 1064*a^2*c/2353 - 1289*a*b^2/2353 - 1289*a*c^2/2353 + 1064*b^3/2353 + 1064*b^2*c/2353)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h4 : 0 ≤ (20043/110591 : ℝ) * (a^2*c + a*b^2 + a*c^2 + b^3 + b^2*c)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1, h2, h3, h4]
example : (∀ (a b c : ℝ), 2 * (a ^ 2 + b * c) * (b ^ 2 + c * a) * (c ^ 2 + a * b) + a ^ 6 + b ^ 6 + c ^ 6 ≥ 0) := @solution
#print axioms solution
