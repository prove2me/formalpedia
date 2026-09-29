-- Prove2me | solution 1 for Rudin.ch08_trigonometric_pi
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T17:38:17.335595+00:00
-- url     : https://prove2.me/submissions/6cb8a581-9673-48b4-ad0f-ad997ebed0a0

import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic
open Filter Topology
noncomputable section
set_option maxHeartbeats 1000000
/-- Rudin, Theorem 8.7: the number `π` is characterized by `cos (π/2) = 0` with `cos` positive
on `[0, π/2)`; the complex exponential has period `2πi`, and `e^{iθ}` parametrizes the unit
circle. -/
theorem solution :
    Real.cos (Real.pi / 2) = 0 ∧
    (∀ x ∈ Set.Ico (0 : ℝ) (Real.pi / 2), 0 < Real.cos x) ∧
    (∀ z : ℂ, Complex.exp (z + 2 * Real.pi * Complex.I) = Complex.exp z) ∧
    (∀ z : ℂ, ‖z‖ = 1 → ∃ t ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      z = Complex.exp (t * Complex.I)) := by
  refine ⟨Real.cos_pi_div_two, ?_, Complex.exp_periodic, ?_⟩
  · intro x hx
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩
  · intro z hz
    have he : Complex.exp ((z.arg : ℂ) * Complex.I) = z := by
      simpa [hz] using Complex.norm_mul_exp_arg_mul_I z
    by_cases ha : 0 ≤ z.arg
    · exact ⟨z.arg, ⟨ha, lt_of_le_of_lt (Complex.arg_le_pi z) (by linarith [Real.pi_pos])⟩, he.symm⟩
    · have hn : z.arg < 0 := lt_of_not_ge ha
      refine ⟨z.arg + 2 * Real.pi, ⟨by linarith [Complex.neg_pi_lt_arg z, Real.pi_pos], by linarith⟩, ?_⟩
      push_cast
      rw [add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one, he]
#print axioms solution
