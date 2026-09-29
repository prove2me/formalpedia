-- Prove2me | solution 1 for WorkbookSource.base_6936
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T09:56:10.713254+00:00
-- url     : https://prove2.me/submissions/1a29d4f0-b7c5-4016-bf1b-86d74b0ecff7

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3) : 9 * (a * b + b * c + c * a) ≤ 22 + 5 * a * b * c  := by
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
  have hsum : 0 ≤ (1058051/441320 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (9805/353056 : ℝ) * (1) * (-a + b)^2 + (2883663/441320 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (3089/1765280 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (139/85 : ℝ) * ((b)) * (-510*a/8201 + b - 7691/8201)^2 + (4085451/42579592 : ℝ) * ((b)) * (1 - a)^2 + (139/85 : ℝ) * ((a)) * (a - 510*b/8201 - 7691/8201)^2 + (4085451/42579592 : ℝ) * ((a)) * (1 - b)^2 := by positivity
  have hid : ( 22 + 5 * a * b * c  ) - ( 9 * (a * b + b * c + c * a) ) = (1058051/441320 : ℝ) * (1) * (-a/2 - b/2 + 1)^2 + (9805/353056 : ℝ) * (1) * (-a + b)^2 + (2883663/441320 : ℝ) * ((-a - b + 3)) * (-a/2 - b/2 + 1)^2 + (3089/1765280 : ℝ) * ((-a - b + 3)) * (-a + b)^2 + (139/85 : ℝ) * ((b)) * (-510*a/8201 + b - 7691/8201)^2 + (4085451/42579592 : ℝ) * ((b)) * (1 - a)^2 + (139/85 : ℝ) * ((a)) * (a - 510*b/8201 - 7691/8201)^2 + (4085451/42579592 : ℝ) * ((a)) * (1 - b)^2 := by
    try simp only [helim]
    <;> ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hab : a + b + c = 3), 9 * (a * b + b * c + c * a) ≤ 22 + 5 * a * b * c) := @solution
#print axioms solution
