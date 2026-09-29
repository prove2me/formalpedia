-- Prove2me | solution 1 for WorkbookSource.base_13088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:51:02.378974+00:00
-- url     : https://prove2.me/submissions/81fadcde-69e4-4eb7-90dc-c75eee323215

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c r p q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = r) (pq : a * b + b * c + c * a = q) (pqr : a + b + c = p) : p * (p + 1) ^ 2 + 12 * r ≥ 4 * q * (p + 2)  := by
  have helim0 : r = (a*b*c) := by
    have hh := habc
    linarith only [hh]
  have helim1 : q = (a*b + a*c + b*c) := by
    have hh := pq
    try simp only [helim0] at hh
    linarith only [hh]
  have helim2 : p = (a + b + c) := by
    have hh := pqr
    try simp only [helim0, helim1] at hh
    linarith only [hh]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim0, helim1, helim2] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim0, helim1, helim2] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (c) := by
    have hh := hc
    try simp only [helim0, helim1, helim2] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1 : ℝ) * ((c)) * (-a - b + c + 1)^2 + (1 : ℝ) * ((b)) * (-a + b - c + 1)^2 + (1 : ℝ) * ((a)) * (a - b - c + 1)^2 := by positivity
  have hid : ( p * (p + 1) ^ 2 + 12 * r ) - ( 4 * q * (p + 2)  ) = (1 : ℝ) * ((c)) * (-a - b + c + 1)^2 + (1 : ℝ) * ((b)) * (-a + b - c + 1)^2 + (1 : ℝ) * ((a)) * (a - b - c + 1)^2 := by
    try simp only [helim0, helim1, helim2]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c r p q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = r) (pq : a * b + b * c + c * a = q) (pqr : a + b + c = p), p * (p + 1) ^ 2 + 12 * r ≥ 4 * q * (p + 2)) := @solution
#print axioms solution
