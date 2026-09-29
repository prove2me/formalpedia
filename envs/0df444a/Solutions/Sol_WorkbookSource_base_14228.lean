-- Prove2me | solution 1 for WorkbookSource.base_14228
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:37:33.052332+00:00
-- url     : https://prove2.me/submissions/a382be74-2c32-49b5-bf59-f54b8f1d57a3

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3):  (a * b + b * c + c * a) / 3 + 3 ≥ a * b * c + a ^ 2 * (b + c) / 2 + b ^ 2 * (c + a) / 2 + c ^ 2 * (a + b) / 2  := by
  have helim : c = (-a - b + 3) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 3) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (147469/263258 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (81625/3159096 : ℝ) * (1) * (-a + b)^2 + (642305/789774 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (41623/3159096 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (123709/394887 : ℝ) * ((b)) * (-32495*a/123709 - 91214*b/123709 + 1)^2 + (394201/8535921 : ℝ) * ((b)) * (-a + b)^2 + (123709/394887 : ℝ) * ((a)) * (-91214*a/123709 - 32495*b/123709 + 1)^2 + (394201/8535921 : ℝ) * ((a)) * (-a + b)^2 := by positivity
  have hid : (  (a * b + b * c + c * a) / 3 + 3 ) - ( a * b * c + a ^ 2 * (b + c) / 2 + b ^ 2 * (c + a) / 2 + c ^ 2 * (a + b) / 2  ) = (147469/263258 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (81625/3159096 : ℝ) * (1) * (-a + b)^2 + (642305/789774 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (41623/3159096 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (123709/394887 : ℝ) * ((b)) * (-32495*a/123709 - 91214*b/123709 + 1)^2 + (394201/8535921 : ℝ) * ((b)) * (-a + b)^2 + (123709/394887 : ℝ) * ((a)) * (-91214*a/123709 - 32495*b/123709 + 1)^2 + (394201/8535921 : ℝ) * ((a)) * (-a + b)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c: ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hab : a + b + c = 3), (a * b + b * c + c * a) / 3 + 3 ≥ a * b * c + a ^ 2 * (b + c) / 2 + b ^ 2 * (c + a) / 2 + c ^ 2 * (a + b) / 2) := @solution
#print axioms solution
