-- Prove2me | solution 1 for WorkbookCorrected.base_709
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:28.534718+00:00
-- url     : https://prove2.me/submissions/f4517d21-266f-41b6-b922-1cfb076976fa

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (a b c d : ℝ) (h1 : (a + b) * (c + d) = 2) (h2 : (a + c) * (b + d) = 3) (h3 : (a + d) * (b + c) = 4) : 7 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  := by
  have hw0 : 0 ≤ (a*c + a*d + b*c + b*d - 2) := by
    have hh := h1
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a*c - a*d - b*c - b*d + 2) := by
    have hh := h1
    try simp only [] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (a*b + a*d + b*c + c*d - 3) := by
    have hh := h2
    try simp only [] at hh
    linarith only [hh]
  have hw3 : 0 ≤ (-a*b - a*d - b*c - c*d + 3) := by
    have hh := h2
    try simp only [] at hh
    linarith only [hh]
  have hw4 : 0 ≤ (a*b + a*c + b*d + c*d - 4) := by
    have hh := h3
    try simp only [] at hh
    linarith only [hh]
  have hw5 : 0 ≤ (-a*b - a*c - b*d - c*d + 4) := by
    have hh := h3
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1 : ℝ) * (1) * (a - b - c + d)^2 + (3 : ℝ) * ((a*b + a*c + b*d + c*d - 4)) * (1)^2 + (1 : ℝ) * ((-a*b - a*d - b*c - c*d + 3)) * (1)^2 + (1 : ℝ) * ((-a*c - a*d - b*c - b*d + 2)) * (1)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  ) - ( 7 ) = (1 : ℝ) * (1) * (a - b - c + d)^2 + (3 : ℝ) * ((a*b + a*c + b*d + c*d - 4)) * (1)^2 + (1 : ℝ) * ((-a*b - a*d - b*c - c*d + 3)) * (1)^2 + (1 : ℝ) * ((-a*c - a*d - b*c - b*d + 2)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (a b c d : ℝ) (h1 : (a + b) * (c + d) = 2) (h2 : (a + c) * (b + d) = 3) (h3 : (a + d) * (b + c) = 4), 7 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ∧ (∃ a b c d : ℝ, ((a + b) * (c + d) = 2) ∧ ((a + c) * (b + d) = 3) ∧ ((a + d) * (b + c) = 4) ∧ ( 7  =  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  )) := by
  constructor
  · exact p2mUpperBound
  · have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    refine ⟨(1 + Real.sqrt 2)/2, (3 + Real.sqrt 2)/2, (1 - Real.sqrt 2)/2, (3 - Real.sqrt 2)/2, ?_, ?_, ?_, ?_⟩ <;> nlinarith [hs]
example : ((∀ (a b c d : ℝ) (h1 : (a + b) * (c + d) = 2) (h2 : (a + c) * (b + d) = 3) (h3 : (a + d) * (b + c) = 4), 7 ≤ a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) ∧ (∃ a b c d : ℝ, ((a + b) * (c + d) = 2) ∧ ((a + c) * (b + d) = 3) ∧ ((a + d) * (b + c) = 4) ∧ ( 7  =  a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2  ))) := @solution
#print axioms solution
