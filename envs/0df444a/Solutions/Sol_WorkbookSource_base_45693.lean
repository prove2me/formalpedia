-- Prove2me | solution 1 for WorkbookSource.base_45693
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T11:10:50.757979+00:00
-- url     : https://prove2.me/submissions/846064ef-5e64-4e85-92d3-8dd9e6e7c7db

import Mathlib
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
theorem solution (a b c : ℝ) (h : a^3 * b + b^3 * c + c^3 * a = 0) :
  3 * (a^4 + b^4 + c^4) + 2 * a * b * c * (a + b + c) ≥ 0  := by
  have hw0 : 0 ≤ (a^3*b + a*c^3 + b^3*c) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hw1 : 0 ≤ (-a^3*b - a*c^3 - b^3*c) := by
    have hh := h
    try simp only [] at hh
    linarith only [hh]
  have hsum : 0 ≤ (3 : ℝ) * (1) * (-16*a^2/297 + 53*a*b/162 - 16*b^2/297 + c^2)^2 + (87953/29403 : ℝ) * (1) * (-16*a^2/281 + 4664*a*b/263859 + 57717*a*c/175906 + b^2)^2 + (82945/27819 : ℝ) * (1) * (a^2 + 88*a*b/4695 + 88*a*c/4695 + 3091*b*c/9390)^2 + (827/5577660 : ℝ) * (1) * (682*a*b/827 + 682*a*c/827 + b*c)^2 + (14587/307514988 : ℝ) * (1) * (682*a*b/1509 + a*c)^2 + (203/5378076 : ℝ) * (1) * (a*b)^2 := by positivity
  have hid : (
    3 * (a^4 + b^4 + c^4) + 2 * a * b * c * (a + b + c) ) - ( 0  ) = (3 : ℝ) * (1) * (-16*a^2/297 + 53*a*b/162 - 16*b^2/297 + c^2)^2 + (87953/29403 : ℝ) * (1) * (-16*a^2/281 + 4664*a*b/263859 + 57717*a*c/175906 + b^2)^2 + (82945/27819 : ℝ) * (1) * (a^2 + 88*a*b/4695 + 88*a*c/4695 + 3091*b*c/9390)^2 + (827/5577660 : ℝ) * (1) * (682*a*b/827 + 682*a*c/827 + b*c)^2 + (14587/307514988 : ℝ) * (1) * (682*a*b/1509 + a*c)^2 + (203/5378076 : ℝ) * (1) * (a*b)^2 := by
    try simp only []
    ring
  linarith only [hsum, hid]
example : (∀ (a b c : ℝ) (h : a^3 * b + b^3 * c + c^3 * a = 0), 3 * (a^4 + b^4 + c^4) + 2 * a * b * c * (a + b + c) ≥ 0) := @solution
#print axioms solution
