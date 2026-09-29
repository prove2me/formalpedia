-- Prove2me | solution 1 for WorkbookSource.base_31427
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T00:52:12.974164+00:00
-- url     : https://prove2.me/submissions/573ad77d-d36e-43e4-8507-64dfa5d8d05d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 600000
theorem solution (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (h : u + v + w = 3) : 16 ≥ 7 * u^2 * v^2 * w^2 + 3 * (u^2 * v^2 + u^2 * w^2 + v^2 * w^2)  := by
  have haux0 (u v w : ℝ) (hlow : 0 ≤ u) (hord1 : u ≤ v) (hord2 : v ≤ w) : 0 ≤ (16*u^6/729 + 32*u^5*v/243 + 32*u^5*w/243 - u^4*v^2/243 + 160*u^4*v*w/243 - u^4*w^2/243 - 166*u^3*v^3/729 + 158*u^3*v^2*w/243 + 158*u^3*v*w^2/243 - 166*u^3*w^3/729 - u^2*v^4/243 + 158*u^2*v^3*w/243 - 488*u^2*v^2*w^2/81 + 158*u^2*v*w^3/243 - u^2*w^4/243 + 32*u*v^5/243 + 160*u*v^4*w/243 + 158*u*v^3*w^2/243 + 158*u*v^2*w^3/243 + 160*u*v*w^4/243 + 32*u*w^5/243 + 16*v^6/729 + 32*v^5*w/243 - v^4*w^2/243 - 166*v^3*w^3/729 - v^2*w^4/243 + 32*v*w^5/243 + 16*w^6/729) := by
    have hdiff1 : 0 ≤ (v - u) := by linarith
    have hdiff2 : 0 ≤ (w - v) := by linarith
    have hpos : 0 ≤ (14/3 : ℝ) * u^4 * (v - u)^2 + (14/3 : ℝ) * u^4 * (v - u)^1 * (w - v)^1 + (14/3 : ℝ) * u^4 * (w - v)^2 + (328/27 : ℝ) * u^3 * (v - u)^3 + (164/9 : ℝ) * u^3 * (v - u)^2 * (w - v)^1 + (172/9 : ℝ) * u^3 * (v - u)^1 * (w - v)^2 + (176/27 : ℝ) * u^3 * (w - v)^3 + (290/27 : ℝ) * u^2 * (v - u)^4 + (580/27 : ℝ) * u^2 * (v - u)^3 * (w - v)^1 + (226/9 : ℝ) * u^2 * (v - u)^2 * (w - v)^2 + (388/27 : ℝ) * u^2 * (v - u)^1 * (w - v)^3 + (62/27 : ℝ) * u^2 * (w - v)^4 + (268/81 : ℝ) * u^1 * (v - u)^5 + (670/81 : ℝ) * u^1 * (v - u)^4 * (w - v)^1 + (940/81 : ℝ) * u^1 * (v - u)^3 * (w - v)^2 + (740/81 : ℝ) * u^1 * (v - u)^2 * (w - v)^3 + (266/81 : ℝ) * u^1 * (v - u)^1 * (w - v)^4 + (32/81 : ℝ) * u^1 * (w - v)^5 + (52/729 : ℝ) * (v - u)^6 + (52/243 : ℝ) * (v - u)^5 * (w - v)^1 + (227/243 : ℝ) * (v - u)^4 * (w - v)^2 + (1102/729 : ℝ) * (v - u)^3 * (w - v)^3 + (239/243 : ℝ) * (v - u)^2 * (w - v)^4 + (64/243 : ℝ) * (v - u)^1 * (w - v)^5 + (16/729 : ℝ) * (w - v)^6 := by positivity
    convert hpos using 1 <;> ring
  have hp : 0 ≤ (16*u^6/729 + 32*u^5*v/243 + 32*u^5*w/243 - u^4*v^2/243 + 160*u^4*v*w/243 - u^4*w^2/243 - 166*u^3*v^3/729 + 158*u^3*v^2*w/243 + 158*u^3*v*w^2/243 - 166*u^3*w^3/729 - u^2*v^4/243 + 158*u^2*v^3*w/243 - 488*u^2*v^2*w^2/81 + 158*u^2*v*w^3/243 - u^2*w^4/243 + 32*u*v^5/243 + 160*u*v^4*w/243 + 158*u*v^3*w^2/243 + 158*u*v^2*w^3/243 + 160*u*v*w^4/243 + 32*u*w^5/243 + 16*v^6/729 + 32*v^5*w/243 - v^4*w^2/243 - 166*v^3*w^3/729 - v^2*w^4/243 + 32*v*w^5/243 + 16*w^6/729) := by
    rcases le_total u v with hab | hba
    · rcases le_total v w with hbc | hcb
      ·
        convert haux0 u v w (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total u w with hac | hca
        ·
          convert haux0 u w v (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 w u v (by positivity) (by linarith) (by linarith) using 1 <;> ring
    · rcases le_total u w with hbc | hcb
      ·
        convert haux0 v u w (by positivity) (by linarith) (by linarith) using 1 <;> ring
      · rcases le_total v w with hac | hca
        ·
          convert haux0 v w u (by positivity) (by linarith) (by linarith) using 1 <;> ring
        ·
          convert haux0 w v u (by positivity) (by linarith) (by linarith) using 1 <;> ring
  have he : (-7*u^2*v^2*w^2 - 3*u^2*v^2 - 3*u^2*w^2 - 3*v^2*w^2 + 16) = (16*u^6/729 + 32*u^5*v/243 + 32*u^5*w/243 - u^4*v^2/243 + 160*u^4*v*w/243 - u^4*w^2/243 - 166*u^3*v^3/729 + 158*u^3*v^2*w/243 + 158*u^3*v*w^2/243 - 166*u^3*w^3/729 - u^2*v^4/243 + 158*u^2*v^3*w/243 - 488*u^2*v^2*w^2/81 + 158*u^2*v*w^3/243 - u^2*w^4/243 + 32*u*v^5/243 + 160*u*v^4*w/243 + 158*u*v^3*w^2/243 + 158*u*v^2*w^3/243 + 160*u*v*w^4/243 + 32*u*w^5/243 + 16*v^6/729 + 32*v^5*w/243 - v^4*w^2/243 - 166*v^3*w^3/729 - v^2*w^4/243 + 32*v*w^5/243 + 16*w^6/729) := by
    linear_combination (-16*u^5/729 - 80*u^4*v/729 - 80*u^4*w/729 - 16*u^4/243 + 83*u^3*v^2/729 - 320*u^3*v*w/729 - 64*u^3*v/243 + 83*u^3*w^2/729 - 64*u^3*w/243 - 16*u^3/81 + 83*u^2*v^3/729 - 79*u^2*v^2*w/243 + 49*u^2*v^2/81 - 79*u^2*v*w^2/243 - 64*u^2*v*w/81 - 16*u^2*v/27 + 83*u^2*w^3/729 + 49*u^2*w^2/81 - 16*u^2*w/27 - 16*u^2/27 - 80*u*v^4/729 - 320*u*v^3*w/729 - 64*u*v^3/243 - 79*u*v^2*w^2/243 - 64*u*v^2*w/81 - 16*u*v^2/27 - 320*u*v*w^3/729 - 64*u*v*w^2/81 - 32*u*v*w/27 - 32*u*v/27 - 80*u*w^4/729 - 64*u*w^3/243 - 16*u*w^2/27 - 32*u*w/27 - 16*u/9 - 16*v^5/729 - 80*v^4*w/729 - 16*v^4/243 + 83*v^3*w^2/729 - 64*v^3*w/243 - 16*v^3/81 + 83*v^2*w^3/729 + 49*v^2*w^2/81 - 16*v^2*w/27 - 16*v^2/27 - 80*v*w^4/729 - 64*v*w^3/243 - 16*v*w^2/27 - 32*v*w/27 - 16*v/9 - 16*w^5/729 - 16*w^4/243 - 16*w^3/81 - 16*w^2/27 - 16*w/9 - 16/3) * h
  nlinarith only [hp, he]
example : (∀ (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) (h : u + v + w = 3), 16 ≥ 7 * u^2 * v^2 * w^2 + 3 * (u^2 * v^2 + u^2 * w^2 + v^2 * w^2)) := @solution
#print axioms solution
