-- Prove2me | solution 1 for WorkbookCorrected.base_46350
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:26.247222+00:00
-- url     : https://prove2.me/submissions/050a68ed-a29a-4063-8932-0fb1b20f0a2b

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (a b c : ℝ) (h : a^2 + b^2 + c^2 + 4 * a * b = 128) :
  a * b + b * c + c * a ≤ 64  := by
  have hw0 : 0 ≤ (a^2 + 4*a*b + b^2 + c^2 - 128) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a^2 - 4*a*b - b^2 - c^2 + 128) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (1/2 : ℝ) * (1) * (-a - b + c)^2 + (1/2 : ℝ) * ((-a^2 - 4*a*b - b^2 - c^2 + 128)) * (1)^2 := by positivity
  have hid : ( 64  ) - (
    a * b + b * c + c * a ) = (1/2 : ℝ) * (1) * (-a - b + c)^2 + (1/2 : ℝ) * ((-a^2 - 4*a*b - b^2 - c^2 + 128)) * (1)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 + 4 * a * b = 128), a * b + b * c + c * a ≤ 64) ∧ (∃ a b c : ℝ, (a^2 + b^2 + c^2 + 4 * a * b = 128) ∧ (
  a * b + b * c + c * a  =  64  )) := by
  constructor
  · exact p2mUpperBound
  · refine ⟨0, 8, 8, ?_⟩ <;> norm_num
example : ((∀ (a b c : ℝ) (h : a^2 + b^2 + c^2 + 4 * a * b = 128), a * b + b * c + c * a ≤ 64) ∧ (∃ a b c : ℝ, (a^2 + b^2 + c^2 + 4 * a * b = 128) ∧ (
  a * b + b * c + c * a  =  64  ))) := @solution
#print axioms solution
