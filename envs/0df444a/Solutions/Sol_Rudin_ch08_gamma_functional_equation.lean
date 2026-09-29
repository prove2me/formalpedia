-- Prove2me | solution 1 for Rudin.ch08_gamma_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:15.813057+00:00
-- url     : https://prove2.me/submissions/135a4133-4e9d-48bb-8404-91d624b6bcd6

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
/-- Rudin, Theorem 8.18: the Gamma function satisfies `Γ(x+1) = x Γ(x)` for `x > 0`,
`Γ(n+1) = n!` for nonnegative integers `n`, and `log Γ` is convex on `(0, ∞)`. -/
theorem solution :
    (∀ x : ℝ, 0 < x → Real.Gamma (x + 1) = x * Real.Gamma x) ∧
    (∀ n : ℕ, Real.Gamma (n + 1) = n.factorial) ∧
    ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (Real.Gamma x)) := by
  exact ⟨fun x hx => Real.Gamma_add_one (ne_of_gt hx),
    Real.Gamma_nat_eq_factorial, Real.convexOn_log_Gamma⟩
#print axioms solution
