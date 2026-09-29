-- Prove2me | solution 1 for Rudin.ch08_exp_properties
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:17.94432+00:00
-- url     : https://prove2.me/submissions/d55fdba3-6560-49f7-8348-c6e9b3428d37

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
/-- Rudin, Theorem 8.6: the exponential function satisfies the addition formula, is its own
derivative, is positive and strictly increasing on the real line with limits `+∞` and `0` at
`±∞`, and grows faster than every power. -/
theorem solution :
    (∀ z w : ℂ, Complex.exp (z + w) = Complex.exp z * Complex.exp w) ∧
    (∀ x : ℝ, HasDerivAt Real.exp (Real.exp x) x) ∧
    StrictMono Real.exp ∧
    Tendsto Real.exp atTop atTop ∧
    Tendsto Real.exp atBot (𝓝 0) ∧
    (∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x)) atTop (𝓝 0)) := by
  exact ⟨Complex.exp_add, Real.hasDerivAt_exp, Real.exp_strictMono,
    Real.tendsto_exp_atTop, Real.tendsto_exp_atBot,
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero⟩
#print axioms solution
