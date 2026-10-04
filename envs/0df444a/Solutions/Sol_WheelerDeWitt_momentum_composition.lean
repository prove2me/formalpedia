-- Prove2me | solution 1 for WheelerDeWitt.momentum_composition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T00:29:03.929283+00:00
-- url     : https://prove2.me/submissions/bbdb3d68-7658-4f8e-8925-8a7e8e7000ff

import Mathlib
import Definitions.Def_wdw_canonical_operators
set_option autoImplicit false

open WheelerDeWitt in
theorem solution {C X : Type*} (D : FunctionalDerivative C X)
    (hbar : ℝ) (x : X) (a b c d : Fin 3) (psi : Wavefunction C) (q : C) :
    (momentum D hbar x a b (momentum D hbar x c d psi)) q =
      -(hbar : ℂ)^2 * (D x a b (D x c d psi)) q := by
  simp only [momentum, LinearMap.smul_apply, map_smul, Pi.smul_apply, smul_eq_mul]
  linear_combination ((hbar : ℂ)^2 * (D x a b (D x c d psi)) q) * Complex.I_sq
