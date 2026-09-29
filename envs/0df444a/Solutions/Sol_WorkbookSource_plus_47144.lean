-- Prove2me | solution 1 for WorkbookSource.plus_47144
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:53.067966+00:00
-- url     : https://prove2.me/submissions/0c3e033e-bd6d-4bdb-b91b-2685d3541021

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4) : a * b * c * d + 1 / 3 * (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 3 / 4 * (a * b * c + a * b * d + a * c * d + b * c * d)   := by
  have helim : d = (-a - b - c + 4) := by linarith only [hab]
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
  have hw3 : 0 ≤ (-a - b - c + 4) := by
    have hh := hd
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (4/3 : ℝ) * (1) * (a^2/8 + a*b/2 - a*c/4 - a/2 + b^2/8 - b*c/4 - b/2 - c^2/4 + c)^2 + (1 : ℝ) * (1) * (a^2/4 + a*c/2 - a - b^2/4 - b*c/2 + b)^2 + (1/3 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/48 : ℝ) * ((b) * (c)) * (-b + c)^2 + (1/3 : ℝ) * ((a) * (-a - b - c + 4)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/48 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1/48 : ℝ) * ((a) * (b)) * (-a + b)^2 := by positivity
  have hid : ( a * b * c * d + 1 / 3 * (a * b + a * c + a * d + b * c + b * d + c * d) ) - ( 3 / 4 * (a * b * c + a * b * d + a * c * d + b * c * d)   ) = (4/3 : ℝ) * (1) * (a^2/8 + a*b/2 - a*c/4 - a/2 + b^2/8 - b*c/4 - b/2 - c^2/4 + c)^2 + (1 : ℝ) * (1) * (a^2/4 + a*c/2 - a - b^2/4 - b*c/2 + b)^2 + (1/3 : ℝ) * ((c) * (-a - b - c + 4)) * (-a/4 - b/4 - c/2 + 1)^2 + (1/3 : ℝ) * ((b) * (-a - b - c + 4)) * (-a/4 - b/2 - c/4 + 1)^2 + (1/48 : ℝ) * ((b) * (c)) * (-b + c)^2 + (1/3 : ℝ) * ((a) * (-a - b - c + 4)) * (-a/2 - b/4 - c/4 + 1)^2 + (1/48 : ℝ) * ((a) * (c)) * (-a + c)^2 + (1/48 : ℝ) * ((a) * (b)) * (-a + b)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) (hd : d ≥ 0) (hab : a + b + c + d = 4), a * b * c * d + 1 / 3 * (a * b + a * c + a * d + b * c + b * d + c * d) ≥ 3 / 4 * (a * b * c + a * b * d + a * c * d + b * c * d)) := @solution
#print axioms solution
