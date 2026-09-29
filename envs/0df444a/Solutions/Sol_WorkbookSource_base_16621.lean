-- Prove2me | solution 1 for WorkbookSource.base_16621
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:44:37.297384+00:00
-- url     : https://prove2.me/submissions/0b369deb-a8de-4fca-b1ac-03f6c36efbea

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) (hq : q = a * b + b * c + c * a) : 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ≤ q ^ 2 - 19 * q + 156  := by
  have helim0 : c = (-a - b + 6) := by
    have hh := hab
    linarith only [hh]
  have helim1 : q = (-a^2 - a*b + 6*a - b^2 + 6*b) := by
    have hh := hq
    try simp only [helim0] at hh
    linarith only [hh]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 6) := by
    have hh := hc
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hsum : 0 ≤ (156 : ℝ) * (1) * (a^2/52 + 2*a*b/13 - 19*a/52 + 3*b^2/52 - 31*b/52 + 1)^2 + (841/52 : ℝ) * (1) * (-7*a^2/29 - 4*a*b/29 + a + 5*b^2/29 - 17*b/29)^2 := by positivity
  have hid : ( q ^ 2 - 19 * q + 156  ) - ( 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ) = (156 : ℝ) * (1) * (a^2/52 + 2*a*b/13 - 19*a/52 + 3*b^2/52 - 31*b/52 + 1)^2 + (841/52 : ℝ) * (1) * (-7*a^2/29 - 4*a*b/29 + a + 5*b^2/29 - 17*b/29)^2 := by
    try simp only [helim0, helim1]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 6) (hq : q = a * b + b * c + c * a), 2 * (a * b ^ 2 + b * c ^ 2 + c * a ^ 2) + 3 * a * b * c ≤ q ^ 2 - 19 * q + 156) := @solution
#print axioms solution
