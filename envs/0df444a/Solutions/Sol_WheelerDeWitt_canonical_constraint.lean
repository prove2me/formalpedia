-- Prove2me | solution 1 for WheelerDeWitt.canonical_constraint
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T00:12:49.411935+00:00
-- url     : https://prove2.me/submissions/49171ddf-4263-498f-903b-b530fc4b717e

import Theorems.Thm_WheelerDeWitt_momentum_composition
import Mathlib.Tactic.Ring

set_option autoImplicit false
open WheelerDeWitt

theorem solution {C X : Type*} [Nonempty C] [Nonempty X]
    (g : Geometry C X) (D : FunctionalDerivative C X)
    (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (hkappa : 0 < kappa) (hhbar : 0 < hbar)
    (psi : Wavefunction C) (q : C) (x : X) :
    quantizedHamiltonian g D rho kappa hbar cosmologicalConstant psi q x =
      wheelerDeWittExpression g D rho kappa hbar cosmologicalConstant psi q x := by
  simp only [quantizedHamiltonian, wheelerDeWittExpression, momentum_composition]
  have pull (u v : ℂ) : u * (-(hbar : ℂ)^2 * v) = -(hbar : ℂ)^2 * (u * v) := by
    ring
  simp_rw [pull, ← Finset.mul_sum]
  ring
