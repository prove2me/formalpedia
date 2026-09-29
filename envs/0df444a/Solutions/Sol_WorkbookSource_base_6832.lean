-- Prove2me | solution 1 for WorkbookSource.base_6832
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:52:08.337297+00:00
-- url     : https://prove2.me/submissions/2f24e060-0e84-4849-bfa8-9845c51b2cf5

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1) :  (1 + a) * (1 + b) * (1 + c) ≥ (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2  := by
  have helim : c = (-a - b + 1) := by linarith only [habc]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 1) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1/2 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (2 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (2 : ℝ) * ((b) * (-a - b + 1)) * (a/2 + b - 1/2)^2 + (2 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 + (2 : ℝ) * ((a) * (-a - b + 1)) * (a + b/2 - 1/2)^2 + (1/2 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : (  (1 + a) * (1 + b) * (1 + c) ) - ( (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2  ) = (1/2 : ℝ) * ((-a - b + 1)) * (-a + b)^2 + (2 : ℝ) * ((b)) * (a + b/2 - 1/2)^2 + (2 : ℝ) * ((b) * (-a - b + 1)) * (a/2 + b - 1/2)^2 + (2 : ℝ) * ((a)) * (a/2 + b - 1/2)^2 + (2 : ℝ) * ((a) * (-a - b + 1)) * (a + b/2 - 1/2)^2 + (1/2 : ℝ) * ((a) * (b)) * (-a + b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a + b + c = 1), (1 + a) * (1 + b) * (1 + c) ≥ (1 - a ^ 2) ^ 2 + (1 - b ^ 2) ^ 2 + (1 - c ^ 2) ^ 2) := @solution
#print axioms solution
