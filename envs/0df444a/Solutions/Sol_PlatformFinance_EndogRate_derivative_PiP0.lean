-- Prove2me | solution 1 for PlatformFinance.EndogRate.derivative_PiP0
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:49:26.316471+00:00
-- url     : https://prove2.me/submissions/d99efc20-5dfd-4e82-820b-0013ee576452

import Mathlib
import Definitions.Def_PlatformFinance_EndogRate_Model
set_option autoImplicit false
open PlatformFinance.EndogRate

theorem solution (a φ c rf r : ℝ) (hφ1 : φ < 1) (hr : -1 < r) :
    HasDerivAt (PiP0 a φ c rf) (G1 a φ c rf r / (8 * (1 - φ) ^ 2 * (1 + r) ^ 2)) r := by
  have hid : HasDerivAt (fun x : ℝ => x) 1 r := hasDerivAt_id r
  have hN1 : HasDerivAt (fun x : ℝ => a * (1 - φ) - c * (1 + x)) (-c) r := by
    have := ((hid.const_add 1).const_mul c).const_sub (a * (1 - φ))
    simpa using this
  have hA : HasDerivAt (fun x : ℝ => a * (1 - φ) * (x * (φ + 2) - 2 * rf * (1 - φ) + 3 * φ))
      (a * (1 - φ) * (φ + 2)) r := by
    have := (((hid.mul_const (φ + 2)).sub_const (2 * rf * (1 - φ))).add_const (3 * φ)).const_mul
      (a * (1 - φ))
    simpa using this
  have hB1 : HasDerivAt (fun x : ℝ => c * (x + 1)) c r := by
    have := (hid.add_const 1).const_mul c
    simpa using this
  have hB2 : HasDerivAt (fun x : ℝ => x * (φ - 2) + 2 * rf * (1 - φ) - φ) (φ - 2) r := by
    have := ((hid.mul_const (φ - 2)).add_const (2 * rf * (1 - φ))).sub_const φ
    simpa using this
  have hB := hB1.mul hB2
  have hN2 := hA.sub hB
  have hN := hN1.mul hN2
  have hD : HasDerivAt (fun x : ℝ => 16 * (x + 1) * (1 - φ) ^ 2) (16 * (1 - φ) ^ 2) r := by
    have := ((hid.add_const 1).const_mul 16).mul_const ((1 - φ) ^ 2)
    simpa using this
  have hr1 : r + 1 ≠ 0 := by linarith
  have h1φ : 1 - φ ≠ 0 := by linarith
  have hDne : 16 * (r + 1) * (1 - φ) ^ 2 ≠ 0 := by positivity
  have := hN.div hD hDne
  refine HasDerivAt.congr_deriv (f := PiP0 a φ c rf) this ?_
  simp only [Pi.mul_apply, Pi.sub_apply, G1]
  have h1r : 1 + r ≠ 0 := by linarith
  field_simp
  ring
