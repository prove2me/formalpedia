-- Prove2me | solution 1 for Wigner.wigner_real
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T17:48:45.935032+00:00
-- url     : https://prove2.me/submissions/5d489b5a-e007-4258-8931-63d59ec9047a

import Mathlib
import Definitions.Def_wigner

open MeasureTheory
open Wigner

open ComplexConjugate

theorem solution {ψ : ℝ → ℂ} {ℏ x p : ℝ} (hℏ : 0 < ℏ)
    (hint : Integrable (fun y => wignerIntegrand ψ ℏ x p y) volume) :
    (wignerIntegral ψ ℏ x p).im = 0 := by
  have hsym : ∀ y, wignerIntegrand ψ ℏ x p (-y) = conj (wignerIntegrand ψ ℏ x p y) := by
    intro y
    simp only [wignerIntegrand, map_mul, Complex.conj_conj, ← Complex.exp_conj, Complex.conj_I,
      Complex.conj_ofReal]
    rw [show x + -y = x - y by ring, show x - -y = x + y by ring]
    have : Complex.ofReal (2 * p * -y / ℏ) * Complex.I = Complex.ofReal (2 * p * y / ℏ) * -Complex.I := by
      push_cast; ring
    rw [this]; ring
  have h1 : wignerIntegral ψ ℏ x p = conj (wignerIntegral ψ ℏ x p) := by
    unfold wignerIntegral
    rw [← integral_conj, ← integral_neg_eq_self]
    simp only [hsym]
  have := congrArg Complex.im h1
  rw [Complex.conj_im] at this
  linarith
