-- Prove2me | solution 1 for Rudin.ch08_bohr_mollerup
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:15.059982+00:00
-- url     : https://prove2.me/submissions/8f2801e8-8caf-44cf-9594-5413dc3deb6c

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
/-- Rudin, Theorem 8.19 (Bohr–Mollerup): a positive function `f` on `(0, ∞)` with
`f 1 = 1`, `f (x + 1) = x f x` and `log f` convex is the Gamma function. -/
theorem solution (f : ℝ → ℝ) (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hone : f 1 = 1) (hrec : ∀ x : ℝ, 0 < x → f (x + 1) = x * f x)
    (hconv : ConvexOn ℝ (Set.Ioi (0 : ℝ)) (fun x => Real.log (f x))) :
    ∀ x : ℝ, 0 < x → f x = Real.Gamma x := by
  intro x hx
  exact Real.eq_Gamma_of_log_convex hconv (fun {y} hy => hrec y hy)
    (fun {y} hy => hpos y hy) hone hx
#print axioms solution
