-- Prove2me | solution 1 for WorkbookSource.plus_59988
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T10:33:53.754152+00:00
-- url     : https://prove2.me/submissions/2843bf6c-24f1-4a8e-8f4c-c80709ee42f9

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hab : a + b + c + d = 1) (k : ℝ) (hk : 1 ≤ k) : a * b + k * b * c + c * d ≤ k / 4   := by
  have helim : d = (-a - b - c + 1) := by linarith only [hab]
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
  have hw3 : 0 ≤ (-a - b - c + 1) := by
    have hh := hd
    try simp only [helim] at hh
    linarith only [hh]
  have hw4 : 0 ≤ (k - 1) := by
    have hh := hk
    try simp only [helim] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (a + c - 1/2)^2 + (1/4 : ℝ) * ((k - 1)) * (-b + c)^2 + (1/4 : ℝ) * ((-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((c) * (-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((b) * (-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (k - 1)) * (1)^2 + (1 : ℝ) * ((a) * (-a - b - c + 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (c) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (b) * (k - 1)) * (1)^2 := by positivity
  have hid : ( k / 4   ) - ( a * b + k * b * c + c * d ) = (1 : ℝ) * (1) * (a + c - 1/2)^2 + (1/4 : ℝ) * ((k - 1)) * (-b + c)^2 + (1/4 : ℝ) * ((-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((c) * (-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((b) * (-a - b - c + 1) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (k - 1)) * (1)^2 + (1 : ℝ) * ((a) * (-a - b - c + 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (c) * (k - 1)) * (1)^2 + (1/4 : ℝ) * ((a) * (b) * (k - 1)) * (1)^2 := by
    try simp only [helim]
    ring
  linarith only [hsum, hid]
example : (∀ (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (hab : a + b + c + d = 1) (k : ℝ) (hk : 1 ≤ k), a * b + k * b * c + c * d ≤ k / 4) := @solution
#print axioms solution
