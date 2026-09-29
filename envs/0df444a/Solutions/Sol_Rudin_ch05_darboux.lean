-- Prove2me | solution 1 for Rudin.ch05_darboux
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:39:24.002636+00:00
-- url     : https://prove2.me/submissions/17408774-e8bc-42db-81b2-9e05fef28962

import Mathlib
set_option autoImplicit false
open Filter Topology
theorem solution (a b : ℝ) (hab : a < b) (f : ℝ → ℝ)
    (hfd : ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ f x) (A : ℝ)
    (hA : deriv f a < A ∧ A < deriv f b) :
    ∃ x ∈ Set.Ioo a b, deriv f x = A := by
  exact exists_hasDerivWithinAt_eq_of_gt_of_lt hab.le
    (fun x hx => (hfd x hx).hasDerivAt.hasDerivWithinAt) hA.1 hA.2
#print axioms solution
