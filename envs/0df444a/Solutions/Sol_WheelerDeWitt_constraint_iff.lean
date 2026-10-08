-- Prove2me | solution 1 for WheelerDeWitt.constraint_iff
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-05T00:14:01.704996+00:00
-- url     : https://prove2.me/submissions/1a13822e-cbdd-4ae4-b059-be96d83c8878

import Theorems.Thm_WheelerDeWitt_canonical_constraint

set_option autoImplicit false
open WheelerDeWitt

theorem solution {C X : Type*} [Nonempty C] [Nonempty X]
    (g : Geometry C X) (D : FunctionalDerivative C X)
    (rho : X → Module.End ℂ (Wavefunction C))
    (kappa hbar cosmologicalConstant : ℝ) (hkappa : 0 < kappa) (hhbar : 0 < hbar)
    (psi : Wavefunction C) :
    (∀ q x, quantizedHamiltonian g D rho kappa hbar cosmologicalConstant psi q x = 0) ↔
    (∀ q x, wheelerDeWittExpression g D rho kappa hbar cosmologicalConstant psi q x = 0) := by
  simp only [canonical_constraint g D rho kappa hbar cosmologicalConstant hkappa hhbar psi]
