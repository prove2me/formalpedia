-- Prove2me | solution 1 for WorkbookSource.plus_75566
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:12:17.230175+00:00
-- url     : https://prove2.me/submissions/e21b11d2-56ac-4225-a483-c604ecab439c

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : a^2 + 2 * b = 7) (hb : b^2 + 4 * c = -7) : c^2 + 6 * a ≥ -14   := by
  have hw0 : 0 ≤ (a^2 + 2*b - 7) := by
    have hh := ha
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a^2 - 2*b + 7) := by
    have hh := ha
    try simp only [] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (b^2 + 4*c + 7) := by
    have hh := hb
    try simp only [] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (-b^2 - 4*c - 7) := by
    have hh := hb
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (14 : ℝ) * (1) * (3*a/14 + b/14 + c/7 + 1)^2 + (13/14 : ℝ) * (1) * (-3*a/13 + b - 2*c/13)^2 + (9/13 : ℝ) * (1) * (-2*a/3 + c)^2 + (1 : ℝ) * ((-b^2 - 4*c - 7)) * (1)^2 + (1 : ℝ) * ((-a^2 - 2*b + 7)) * (1)^2 := by positivity
  have hid : ( c^2 + 6 * a ) - ( -14   ) = (14 : ℝ) * (1) * (3*a/14 + b/14 + c/7 + 1)^2 + (13/14 : ℝ) * (1) * (-3*a/13 + b - 2*c/13)^2 + (9/13 : ℝ) * (1) * (-2*a/3 + c)^2 + (1 : ℝ) * ((-b^2 - 4*c - 7)) * (1)^2 + (1 : ℝ) * ((-a^2 - 2*b + 7)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : a^2 + 2 * b = 7) (hb : b^2 + 4 * c = -7), c^2 + 6 * a ≥ -14) := @solution
#print axioms solution
