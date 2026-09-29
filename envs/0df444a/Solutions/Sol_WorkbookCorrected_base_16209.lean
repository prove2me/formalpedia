-- Prove2me | solution 1 for WorkbookCorrected.base_16209
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:29.1055+00:00
-- url     : https://prove2.me/submissions/884e8ed6-fcde-4e98-b300-ceb40997ae97

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (x y : ℝ) (h : x^2 - y^2 = 1) : 8 ≤ (3*x + y)^2  := by
  have hw0 : 0 ≤ (x^2 - y^2 - 1) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-x^2 + y^2 + 1) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (9 : ℝ) * (1) * (x/3 + y)^2 + (8 : ℝ) * ((x^2 - y^2 - 1)) * (1)^2 := by positivity
  have hid : ( (3*x + y)^2  ) - ( 8 ) = (9 : ℝ) * (1) * (x/3 + y)^2 + (8 : ℝ) * ((x^2 - y^2 - 1)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (x y : ℝ) (h : x^2 - y^2 = 1), 8 ≤ (3*x + y)^2) ∧ (∃ x y : ℝ, (x^2 - y^2 = 1) ∧ ( 8  =  (3*x + y)^2  )) := by
  constructor
  · exact p2mUpperBound
  · have hs : (Real.sqrt 2)^2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    refine ⟨3 * Real.sqrt 2 / 4, -Real.sqrt 2 / 4, ?_, ?_⟩ <;> nlinarith [hs]
example : ((∀ (x y : ℝ) (h : x^2 - y^2 = 1), 8 ≤ (3*x + y)^2) ∧ (∃ x y : ℝ, (x^2 - y^2 = 1) ∧ ( 8  =  (3*x + y)^2  ))) := @solution
#print axioms solution
