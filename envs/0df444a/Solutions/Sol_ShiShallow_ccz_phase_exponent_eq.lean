-- Prove2me | solution 1 for ShiShallow.ccz_phase_exponent_eq
-- status  : ACCEPTED   (prove)
-- author  : @Goku
-- created : 2026-09-13T03:49:03.369006+00:00
-- url     : https://prove2.me/submissions/0161c27b-d8b9-4508-a511-38b8b72eba9a

import Definitions.Def_ShiShallow_Core

set_option autoImplicit false

private lemma shiCCZ_omega_pow_four :
    Complex.exp (Complex.I * Real.pi / 4) ^ 4 = -1 := by
  have h1 : Complex.exp (Complex.I * Real.pi / 4) ^ 4
      = Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)
        * (Complex.exp (Complex.I * Real.pi / 4) * Complex.exp (Complex.I * Real.pi / 4)) := by
    ring
  rw [h1, ← Complex.exp_add, ← Complex.exp_add,
      (show Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4
          + (Complex.I * Real.pi / 4 + Complex.I * Real.pi / 4)
        = Real.pi * Complex.I by ring)]
  exact Complex.exp_pi_mul_I

private lemma shiCCZ_omega_pow_eight :
    Complex.exp (Complex.I * Real.pi / 4) ^ 8 = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) ^ 8
      = (Complex.exp (Complex.I * Real.pi / 4) ^ 4) ^ 2 := by ring
  rw [h, shiCCZ_omega_pow_four]
  norm_num

private lemma shiCCZ_omega_pow_sixteen :
    Complex.exp (Complex.I * Real.pi / 4) ^ 16 = 1 := by
  have h : Complex.exp (Complex.I * Real.pi / 4) ^ 16
      = (Complex.exp (Complex.I * Real.pi / 4) ^ 8) ^ 2 := by ring
  rw [h, shiCCZ_omega_pow_eight]
  norm_num

theorem solution (a b c : Bool) :
    Complex.exp (Complex.I * Real.pi / 4) ^
        ((if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0)
          + 7 * (if xor a b then 1 else 0) + 7 * (if xor b c then 1 else 0)
          + 7 * (if xor a c then 1 else 0) + (if xor a (xor b c) then 1 else 0))
      = if (a && b && c) then (-1 : ℂ) else 1 := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact shiCCZ_omega_pow_four
      | exact shiCCZ_omega_pow_sixteen
      | exact pow_zero _
