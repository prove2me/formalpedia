-- Prove2me | solution 1 for Section5FiniteProbability.exponential_midpoint
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:22:00.881027+00:00
-- url     : https://prove2.me/submissions/28c35310-93f8-410a-91a5-e543b1f7b316

import Mathlib
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory
theorem solution (a b : ℝ) :
    Real.exp ((a+b)/2) ≤ (Real.exp a+Real.exp b)/2 := by
  have ha : Real.exp (a/2)^2=Real.exp a := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hb : Real.exp (b/2)^2=Real.exp b := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  have hab : Real.exp ((a+b)/2)=Real.exp (a/2)*Real.exp (b/2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hab]
  nlinarith [sq_nonneg (Real.exp (a/2)-Real.exp (b/2))]
