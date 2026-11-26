-- Prove2me | solution 1 for Section5FiniteProbability.law_integral
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-26T19:38:23.055172+00:00
-- url     : https://prove2.me/submissions/67d6948f-2b4d-429e-ada6-3f5da9961f53

import Definitions.Def_Section5Verified_Section5FiniteProbabilityLaw
import Mathlib
section
set_option autoImplicit false

/-! Finite real probability weights as an actual probability measure, with
exact finite-sum integral and event-probability formulas. -/

namespace Section5FiniteProbability

open MeasureTheory

variable {Ω : Type*} [Fintype Ω]



@[simp] theorem mass_apply (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (x : Ω) :
    mass p hp hs x=ENNReal.ofReal (p x) := rfl









end Section5FiniteProbability

end
set_option autoImplicit false
namespace Section5FiniteProbability
end Section5FiniteProbability
open Section5FiniteProbability
open MeasureTheory
variable {Ω : Type*} [Fintype Ω]
theorem solution [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (p : Ω → ℝ) (hp : ∀ x, 0 ≤ p x) (hs : ∑ x, p x=1) (f : Ω → ℝ) :
    (∫ x, f x ∂Section5FiniteProbability.law p hp hs)=∑ x, p x*f x := by
  rw [Section5FiniteProbability.law,PMF.integral_eq_sum]
  simp only [Section5FiniteProbability.mass_apply,ENNReal.toReal_ofReal (hp _),smul_eq_mul]
