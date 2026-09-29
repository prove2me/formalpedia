-- Prove2me | solution 1 for WorkbookCorrected.plus_76546
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:14:24.849902+00:00
-- url     : https://prove2.me/submissions/c2aac432-7dd6-484b-bcc7-3c8e528abf5d

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
private lemma p2mUpperBound (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3) : 9 / 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c   := by
  have helim0 : c = (-a - b + 3) := by
    have hh := habc
    linarith only [hh]
  have hw0 : 0 ≤ (a) := by
    have hh := ha
    try simp only [helim0] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (b) := by
    have hh := hb
    try simp only [helim0] at hh
    linarith only [hh]
  have hw2 : 0 ≤ (-a - b + 3) := by
    have hh := hc
    try simp only [helim0] at hh
    linarith only [hh]
  have hsum : 0 ≤ (3/2 : ℝ) * ((-a - b + 3)) * (-2*a/3 - 2*b/3 + 1)^2 + (3/2 : ℝ) * ((b)) * (1 - 2*b/3)^2 + (3/2 : ℝ) * ((a)) * (1 - 2*a/3)^2 := by positivity
  have hid : ( a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c   ) - ( 9 / 2 ) = (3/2 : ℝ) * ((-a - b + 3)) * (-2*a/3 - 2*b/3 + 1)^2 + (3/2 : ℝ) * ((b)) * (1 - 2*b/3)^2 + (3/2 : ℝ) * ((a)) * (1 - 2*a/3)^2 := by
    try simp only [helim0]
    ring
  linarith only [hsum, hid]
theorem solution : (∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), 9 / 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c) ∧ (∃ a b c : ℝ, (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (a + b + c = 3) ∧ ( 9 / 2  =  a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c   )) := by
  constructor
  · exact p2mUpperBound
  · refine ⟨0, 3/2, 3/2, ?_⟩ <;> norm_num
example : ((∀ (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (habc : a + b + c = 3), 9 / 2 ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c) ∧ (∃ a b c : ℝ, (0 ≤ a) ∧ (0 ≤ b) ∧ (0 ≤ c) ∧ (a + b + c = 3) ∧ ( 9 / 2  =  a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c   ))) := @solution
#print axioms solution
