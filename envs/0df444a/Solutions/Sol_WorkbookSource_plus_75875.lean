-- Prove2me | solution 1 for WorkbookSource.plus_75875
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:55.08784+00:00
-- url     : https://prove2.me/submissions/b4e5fd5f-197f-4169-95cc-3e7dc190abad

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution {a b c : ℝ} (ha : 2/3 ≤ a) (hb : 2/3 ≤ b) (hc : 2/3 ≤ c) (hab : a + b + c = 3) : (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ≥ a * b + b * c + c * a   := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hw0 : 0 ≤ (a - 2/3) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b - 2/3) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 7/3) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (31/3 : ℝ) * (1) * (3*a^2/62 - 15*a*b/31 + 13*a/62 - 9*b^2/31 + b - 15/31)^2 + (1225/124 : ℝ) * (1) * (-11*a^2/35 - 2*a*b/5 + a + 4*b^2/35 - 2/5)^2 + (1/3 : ℝ) * ((-a - b + 7/3)) * (-a + b)^2 + (3 : ℝ) * ((b - 2/3)) * (-2*a/3 - b/3 + 1)^2 + (3 : ℝ) * ((a - 2/3)) * (-a/3 - 2*b/3 + 1)^2 := by positivity
  have hid : ( (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ) - ( a * b + b * c + c * a   ) = (31/3 : ℝ) * (1) * (3*a^2/62 - 15*a*b/31 + 13*a/62 - 9*b^2/31 + b - 15/31)^2 + (1225/124 : ℝ) * (1) * (-11*a^2/35 - 2*a*b/5 + a + 4*b^2/35 - 2/5)^2 + (1/3 : ℝ) * ((-a - b + 7/3)) * (-a + b)^2 + (3 : ℝ) * ((b - 2/3)) * (-2*a/3 - b/3 + 1)^2 + (3 : ℝ) * ((a - 2/3)) * (-a/3 - 2*b/3 + 1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ {a b c : ℝ} (ha : 2/3 ≤ a) (hb : 2/3 ≤ b) (hc : 2/3 ≤ c) (hab : a + b + c = 3), (a * b) ^ 2 + (b * c) ^ 2 + (c * a) ^ 2 ≥ a * b + b * c + c * a) := @solution
#print axioms solution
