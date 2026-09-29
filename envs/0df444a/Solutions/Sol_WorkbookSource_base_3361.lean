-- Prove2me | solution 1 for WorkbookSource.base_3361
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:32:22.788292+00:00
-- url     : https://prove2.me/submissions/39a227b7-18df-41e2-bafe-55082b873b83

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d e : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (he : e ≥ 0) (hab : a + b + c + d + e = 5) : a * b + c * d + e * a + 25 / 4 ≥ b * c + d * e  := by
  have helim : e = (-a - b - c - d + 5) := by linarith only [hab]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (c) := by
    have hh := hc
    try simp only [helim] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (d) := by
    have hh := hd
    try simp only [helim] at hh
    linarith only [hh]
  have hw4 : 0 ≤ (-a - b - c - d + 5) := by
    have hh := he
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (25/4 : ℝ) * (1) * (-b/5 - c/5 - 2*d/5 + 1)^2 + (1/4 : ℝ) * (1) * (-b + c)^2 + (1/2 : ℝ) * ((c) * (-a - b - c - d + 5)) * (1)^2 + (3/2 : ℝ) * ((c) * (d)) * (1)^2 + (1/2 : ℝ) * ((b) * (-a - b - c - d + 5)) * (1)^2 + (1/2 : ℝ) * ((b) * (d)) * (1)^2 + (1 : ℝ) * ((a) * (-a - b - c - d + 5)) * (1)^2 + (1 : ℝ) * ((a) * (d)) * (1)^2 + (1/2 : ℝ) * ((a) * (c)) * (1)^2 + (3/2 : ℝ) * ((a) * (b)) * (1)^2 := by positivity
  have hid : ( a * b + c * d + e * a + 25 / 4 ) - ( b * c + d * e  ) = (25/4 : ℝ) * (1) * (-b/5 - c/5 - 2*d/5 + 1)^2 + (1/4 : ℝ) * (1) * (-b + c)^2 + (1/2 : ℝ) * ((c) * (-a - b - c - d + 5)) * (1)^2 + (3/2 : ℝ) * ((c) * (d)) * (1)^2 + (1/2 : ℝ) * ((b) * (-a - b - c - d + 5)) * (1)^2 + (1/2 : ℝ) * ((b) * (d)) * (1)^2 + (1 : ℝ) * ((a) * (-a - b - c - d + 5)) * (1)^2 + (1 : ℝ) * ((a) * (d)) * (1)^2 + (1/2 : ℝ) * ((a) * (c)) * (1)^2 + (3/2 : ℝ) * ((a) * (b)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c d e : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (he : e ≥ 0) (hab : a + b + c + d + e = 5), a * b + c * d + e * a + 25 / 4 ≥ b * c + d * e) := @solution
#print axioms solution
