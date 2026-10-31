-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P50.idealComb_rephasing
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-31T00:25:03.505692+00:00
-- url     : https://prove2.me/submissions/5d2cc962-145d-4d6f-8a55-1fc9718e25f6

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P50

set_option autoImplicit false
open QAlgorithms.Papers.Independent.Extend50.P50
open scoped BigOperators

theorem solution (N : ℕ) (hN : 1 ≤ N)
    (r : Fin N → ℤ) (spacing : ℝ) (hspacing : 0 < spacing)
    (a : Fin N → ℂ) (ha : ∑ j : Fin N, Complex.normSq (a j) = 1) :
    ∀ m : ℕ, 0 < m →
      detuningPhaseWave a (idealCombDetuning r spacing)
        ((m : ℝ) * (2 * Real.pi / spacing)) =
      detuningPhaseWave a (idealCombDetuning r spacing) 0 := by
  intro m hm
  simp only [detuningPhaseWave, mul_zero, Complex.ofReal_zero, zero_mul, mul_zero,
    neg_zero, Complex.exp_zero, mul_one]
  congr 1
  funext j
  have hphase : -(Complex.I *
      (((idealCombDetuning r spacing j * ((m : ℝ) * (2 * Real.pi / spacing))) : ℝ) : ℂ)) =
      ((-(r j * (m : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    unfold idealCombDetuning
    push_cast
    have hs : (spacing : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspacing.ne'
    field_simp
    <;> ring
  rw [hphase, Complex.exp_int_mul_two_pi_mul_I]
  simp

#print axioms solution
