-- Prove2me | solution 1 for WorkbookCorrected.base_32021
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:07.929583+00:00
-- url     : https://prove2.me/submissions/5a4a31e9-be63-464f-b8bd-946a601196f0

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h1 : a * b * c = 1) :
  a + b + c + a^3 + b^3 + c^3 ≤ (2 / 3) * (a^2 + b^2 + c^2)^2  := by
  have hw0 : 0 ≤ (a*b*c - 1) := by linarith only [h1]
  have hw1 : 0 ≤ (-a*b*c + 1) := by linarith only [h1]
  have hsum : 0 ≤ (4 : ℝ) * (1) * (-7*a^2/48 - a*b/16 - a*c/16 - a/8 - 7*b^2/48 - b*c/16 - b/8 - 7*c^2/48 - c/8 + 1)^2 + (53/48 : ℝ) * (1) * (-31*a^2/106 - 67*a*b/106 + 21*a*c/106 + 9*a/53 - 31*b^2/106 + 21*b*c/106 + 9*b/53 - 55*c^2/106 + c)^2 + (341/318 : ℝ) * (1) * (-a^2/4 + 39*a*b/124 - 85*a*c/124 + 9*a/62 - 659*b^2/1364 + 21*b*c/124 + b - 287*c^2/1364)^2 + (781/744 : ℝ) * (1) * (-713*a^2/1562 + 39*a*b/142 + 39*a*c/142 + a - 287*b^2/1562 - 103*b*c/142 - 287*c^2/1562)^2 + (5663/28116 : ℝ) * (1) * (-256*a^2/809 - 99*a*b/809 - 99*a*c/809 - 256*b^2/809 - 99*b*c/809 + c^2)^2 + (19355/106788 : ℝ) * (1) * (-256*a^2/553 - 99*a*b/553 - 99*a*c/553 + b^2 - 99*b*c/553)^2 + (45/316 : ℝ) * (1) * (a^2 - a*b/3 - a*c/3 - b*c/3)^2 + (4 : ℝ) * ((a*b*c - 1)) * (1)^2 := by positivity
  have hid : ( (2 / 3) * (a^2 + b^2 + c^2)^2  ) - (
  a + b + c + a^3 + b^3 + c^3 ) = (4 : ℝ) * (1) * (-7*a^2/48 - a*b/16 - a*c/16 - a/8 - 7*b^2/48 - b*c/16 - b/8 - 7*c^2/48 - c/8 + 1)^2 + (53/48 : ℝ) * (1) * (-31*a^2/106 - 67*a*b/106 + 21*a*c/106 + 9*a/53 - 31*b^2/106 + 21*b*c/106 + 9*b/53 - 55*c^2/106 + c)^2 + (341/318 : ℝ) * (1) * (-a^2/4 + 39*a*b/124 - 85*a*c/124 + 9*a/62 - 659*b^2/1364 + 21*b*c/124 + b - 287*c^2/1364)^2 + (781/744 : ℝ) * (1) * (-713*a^2/1562 + 39*a*b/142 + 39*a*c/142 + a - 287*b^2/1562 - 103*b*c/142 - 287*c^2/1562)^2 + (5663/28116 : ℝ) * (1) * (-256*a^2/809 - 99*a*b/809 - 99*a*c/809 - 256*b^2/809 - 99*b*c/809 + c^2)^2 + (19355/106788 : ℝ) * (1) * (-256*a^2/553 - 99*a*b/553 - 99*a*c/553 + b^2 - 99*b*c/553)^2 + (45/316 : ℝ) * (1) * (a^2 - a*b/3 - a*c/3 - b*c/3)^2 + (4 : ℝ) * ((a*b*c - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h1 : a * b * c = 1), a + b + c + a^3 + b^3 + c^3 ≤ (2 / 3) * (a^2 + b^2 + c^2)^2) := @solution
#print axioms solution
