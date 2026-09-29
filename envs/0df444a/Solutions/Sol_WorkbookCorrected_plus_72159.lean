-- Prove2me | solution 1 for WorkbookCorrected.plus_72159
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:26.84632+00:00
-- url     : https://prove2.me/submissions/9a1bca39-08aa-4ef7-b503-3a3f184d9a66

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (a b x y : ℝ) (ha : a^2 + b^2 = 2) (hb : x^2 + y^2 = 2) : (1 - a) * (1 - b) + (1 - x) * (1 - y) ≤ 8   := by
  have hw0 : 0 ≤ (a^2 + b^2 - 2) := by
    have hh := ha
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a^2 - b^2 + 2) := by
    have hh := ha
    try simp only [] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (x^2 + y^2 - 2) := by
    have hh := hb
    try simp only [] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (-x^2 - y^2 + 2) := by
    have hh := hb
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (2 : ℝ) * (1) * (a/4 + b/4 + x/4 + y/4 + 1)^2 + (7/8 : ℝ) * (1) * (-a/7 - b/7 - 5*x/7 + y)^2 + (6/7 : ℝ) * (1) * (-3*a/4 + b - x/4)^2 + (3/8 : ℝ) * (1) * (-a + x)^2 + (1 : ℝ) * ((-x^2 - y^2 + 2)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 2)) * (1)^2 := by positivity
  have hid : ( 8   ) - ( (1 - a) * (1 - b) + (1 - x) * (1 - y) ) = (2 : ℝ) * (1) * (a/4 + b/4 + x/4 + y/4 + 1)^2 + (7/8 : ℝ) * (1) * (-a/7 - b/7 - 5*x/7 + y)^2 + (6/7 : ℝ) * (1) * (-3*a/4 + b - x/4)^2 + (3/8 : ℝ) * (1) * (-a + x)^2 + (1 : ℝ) * ((-x^2 - y^2 + 2)) * (1)^2 + (1 : ℝ) * ((-a^2 - b^2 + 2)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (a b x y : ℝ) (ha : a^2 + b^2 = 2) (hb : x^2 + y^2 = 2), (1 - a) * (1 - b) + (1 - x) * (1 - y) ≤ 8) ∧ (∃ a b x y : ℝ, (a^2 + b^2 = 2) ∧ (x^2 + y^2 = 2) ∧ ( (1 - a) * (1 - b) + (1 - x) * (1 - y)  =  8   )) := by
  constructor
  · exact p2mUpperBound
  · refine ⟨-1, -1, -1, -1, ?_⟩ <;> norm_num
example : ((∀ (a b x y : ℝ) (ha : a^2 + b^2 = 2) (hb : x^2 + y^2 = 2), (1 - a) * (1 - b) + (1 - x) * (1 - y) ≤ 8) ∧ (∃ a b x y : ℝ, (a^2 + b^2 = 2) ∧ (x^2 + y^2 = 2) ∧ ( (1 - a) * (1 - b) + (1 - x) * (1 - y)  =  8   ))) := @solution
#print axioms solution
