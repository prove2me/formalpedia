-- Prove2me | solution 1 for WorkbookCorrected.plus_38115
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:13:51.689985+00:00
-- url     : https://prove2.me/submissions/4dba1c8f-ed16-4578-bda6-3c5d1be33300

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (habc : a * b * c = 1) : a + a^2 + a^3 + b + b^2 + b^3 + c + c^2 + c^3 ≤ (a^2 + b^2 + c^2)^2   := by
  have hw0 : 0 ≤ (a*b*c - 1) := by linarith only [habc]
  have hw1 : 0 ≤ (-a*b*c + 1) := by linarith only [habc]
  have hsum : 0 ≤ (6 : ℝ) * (1) * (-5*a^2/24 - a*b/24 - a*c/24 - a/12 - 5*b^2/24 - b*c/24 - b/12 - 5*c^2/24 - c/12 + 1)^2 + (35/24 : ℝ) * (1) * (-17*a^2/70 - 7*a*b/10 + 11*a*c/70 + a/7 - 17*b^2/70 + 11*b*c/70 + b/7 - 29*c^2/70 + c)^2 + (10/7 : ℝ) * (1) * (-17*a^2/80 + 21*a*b/80 - 59*a*c/80 + a/8 - 31*b^2/80 + 11*b*c/80 + b - 3*c^2/16)^2 + (45/32 : ℝ) * (1) * (-11*a^2/30 + 7*a*b/30 + 7*a*c/30 + a - b^2/6 - 23*b*c/30 - c^2/6)^2 + (2/5 : ℝ) * (1) * (-a^2/8 - a*b/4 - a*c/4 - b^2/8 - b*c/4 + c^2)^2 + (63/160 : ℝ) * (1) * (-a^2/7 - 2*a*b/7 - 2*a*c/7 + b^2 - 2*b*c/7)^2 + (27/70 : ℝ) * (1) * (a^2 - a*b/3 - a*c/3 - b*c/3)^2 + (6 : ℝ) * ((a*b*c - 1)) * (1)^2 := by positivity
  have hid : ( (a^2 + b^2 + c^2)^2   ) - ( a + a^2 + a^3 + b + b^2 + b^3 + c + c^2 + c^3 ) = (6 : ℝ) * (1) * (-5*a^2/24 - a*b/24 - a*c/24 - a/12 - 5*b^2/24 - b*c/24 - b/12 - 5*c^2/24 - c/12 + 1)^2 + (35/24 : ℝ) * (1) * (-17*a^2/70 - 7*a*b/10 + 11*a*c/70 + a/7 - 17*b^2/70 + 11*b*c/70 + b/7 - 29*c^2/70 + c)^2 + (10/7 : ℝ) * (1) * (-17*a^2/80 + 21*a*b/80 - 59*a*c/80 + a/8 - 31*b^2/80 + 11*b*c/80 + b - 3*c^2/16)^2 + (45/32 : ℝ) * (1) * (-11*a^2/30 + 7*a*b/30 + 7*a*c/30 + a - b^2/6 - 23*b*c/30 - c^2/6)^2 + (2/5 : ℝ) * (1) * (-a^2/8 - a*b/4 - a*c/4 - b^2/8 - b*c/4 + c^2)^2 + (63/160 : ℝ) * (1) * (-a^2/7 - 2*a*b/7 - 2*a*c/7 + b^2 - 2*b*c/7)^2 + (27/70 : ℝ) * (1) * (a^2 - a*b/3 - a*c/3 - b*c/3)^2 + (6 : ℝ) * ((a*b*c - 1)) * (1)^2 := by ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (habc : a * b * c = 1), a + a^2 + a^3 + b + b^2 + b^3 + c + c^2 + c^3 ≤ (a^2 + b^2 + c^2)^2) := @solution
#print axioms solution
