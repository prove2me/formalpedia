-- Prove2me | solution 1 for WorkbookSource.base_15179
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T22:44:41.393236+00:00
-- url     : https://prove2.me/submissions/b85874f3-3d11-4d62-8140-fedaf4bddbec

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution {a u v : ℝ} : (3 * a^6 + a^5 * (15 * u + 12 * v) + a^4 * (33 * u^2 + 48 * u * v + 15 * v^2) + a^3 * (39 * u^3 + 81 * u^2 * v + 48 * u * v^2 + 6 * v^3) + a^2 * (25 * u^4 + 68 * u^3 * v + 60 * u^2 * v^2 + 17 * u * v^3 + v^4) + a * (8 * u^5 + 27 * u^4 * v + 32 * u^3 * v^2 + 15 * u^2 * v^3 + 2 * u * v^4) + u^6 + 4 * u^5 * v + 6 * u^4 * v^2 + 4 * u^3 * v^3 + u^2 * v^4) ≥ 0  := by
  have h0 : 0 ≤ (31 : ℝ) * (9*a^3/31 + 51*a^2*u/62 + 18*a^2*v/31 + 22*a*u^2/31 + a*u*v + 11*a*v^2/62 + 11*u^3/62 + 11*u^2*v/31 + 11*u*v^2/62)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  have h1 : 0 ≤ (48/31 : ℝ) * (a^3/2 + a^2*u/8 + a^2*v - a*u^2/2 - a*v^2/8 - u^3/8 - u^2*v/4 - u*v^2/8)^2 := mul_nonneg (by norm_num) (sq_nonneg _)
  nlinarith only [h0, h1]
example : (∀ {a u v : ℝ}, (3 * a^6 + a^5 * (15 * u + 12 * v) + a^4 * (33 * u^2 + 48 * u * v + 15 * v^2) + a^3 * (39 * u^3 + 81 * u^2 * v + 48 * u * v^2 + 6 * v^3) + a^2 * (25 * u^4 + 68 * u^3 * v + 60 * u^2 * v^2 + 17 * u * v^3 + v^4) + a * (8 * u^5 + 27 * u^4 * v + 32 * u^3 * v^2 + 15 * u^2 * v^3 + 2 * u * v^4) + u^6 + 4 * u^5 * v + 6 * u^4 * v^2 + 4 * u^3 * v^3 + u^2 * v^4) ≥ 0) := @solution
#print axioms solution
