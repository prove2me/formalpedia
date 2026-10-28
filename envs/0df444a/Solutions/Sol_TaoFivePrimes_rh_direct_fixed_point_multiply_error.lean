-- Prove2me | solution 1 for TaoFivePrimes.rh_direct_fixed_point_multiply_error
-- status  : ACCEPTED   (prove)
-- author  : @Johan Mercedes
-- created : 2026-10-27T23:33:11.308089+00:00
-- url     : https://prove2.me/submissions/bd811cc7-d789-4f06-a4c4-9b1a9881e877

import Mathlib

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
open Complex

namespace DirectFixedPointMultiply

lemma scalar_rounding (D : ℕ) (hD : 0<D) (N : ℤ) :
    |((N/(D:ℤ):ℤ):ℝ)/(D:ℝ)-(N:ℝ)/(D:ℝ)^2| ≤ 1/(D:ℝ) := by
  have hDi : (0:ℤ)<D := by exact_mod_cast hD
  have hDr : (0:ℝ)<D := by exact_mod_cast hD
  have hr0 : (0:ℝ)≤(N%(D:ℤ):ℤ) := by exact_mod_cast Int.emod_nonneg N (ne_of_gt hDi)
  have hr1 : ((N%(D:ℤ):ℤ):ℝ)≤D := by
    exact_mod_cast (Int.emod_lt_of_pos N hDi).le
  have he : ((N%(D:ℤ):ℤ):ℝ)+(D:ℝ)*((N/(D:ℤ):ℤ):ℝ) = (N:ℝ) := by
    exact_mod_cast Int.emod_add_mul_ediv N (D:ℤ)
  have hid : ((N/(D:ℤ):ℤ):ℝ)/(D:ℝ)-(N:ℝ)/(D:ℝ)^2 =
      -((N%(D:ℤ):ℤ):ℝ)/(D:ℝ)^2 := by
    field_simp
    nlinarith
  rw [hid,abs_div,abs_neg,abs_of_nonneg hr0,abs_of_pos (pow_pos hDr 2)]
  apply (div_le_div_iff₀ (pow_pos hDr 2) hDr).mpr
  nlinarith

end DirectFixedPointMultiply

/-- Multiplying two complex fixed-point values and rounding each resulting
integer component downward costs at most two units at the shared scale. -/
theorem solution (D : ℕ) (hD : 0<D) (a b c d : ℤ) :
    ‖(((a*c-b*d)/(D:ℤ):ℤ):ℂ)/(D:ℂ) +
       Complex.I*(((a*d+b*c)/(D:ℤ):ℤ):ℂ)/(D:ℂ) -
       (((a:ℂ)+Complex.I*(b:ℂ))/(D:ℂ))*(((c:ℂ)+Complex.I*(d:ℂ))/(D:ℂ))‖
       ≤ 2/(D:ℝ) := by
  let x : ℝ := (((a*c-b*d)/(D:ℤ):ℤ):ℝ)/(D:ℝ)-((a*c-b*d:ℤ):ℝ)/(D:ℝ)^2
  let y : ℝ := (((a*d+b*c)/(D:ℤ):ℤ):ℝ)/(D:ℝ)-((a*d+b*c:ℤ):ℝ)/(D:ℝ)^2
  have hx : |x|≤1/(D:ℝ) := DirectFixedPointMultiply.scalar_rounding D hD _
  have hy : |y|≤1/(D:ℝ) := DirectFixedPointMultiply.scalar_rounding D hD _
  have hD0 : (D:ℂ)≠0 := by exact_mod_cast (ne_of_gt hD)
  have hid : (((a*c-b*d)/(D:ℤ):ℤ):ℂ)/(D:ℂ) +
       Complex.I*(((a*d+b*c)/(D:ℤ):ℤ):ℂ)/(D:ℂ) -
       (((a:ℂ)+Complex.I*(b:ℂ))/(D:ℂ))*(((c:ℂ)+Complex.I*(d:ℂ))/(D:ℂ))
       = (x:ℂ)+Complex.I*(y:ℂ) := by
    dsimp [x,y]
    push_cast
    field_simp
    linear_combination -((b:ℂ)*(d:ℂ))*Complex.I_sq
  rw [hid]
  have hh := norm_add_le (x:ℂ) (Complex.I*(y:ℂ))
  simp only [Complex.norm_real,Real.norm_eq_abs,norm_mul,Complex.norm_I,one_mul] at hh
  calc
    _ ≤ |x|+|y| := hh
    _ ≤ 1/(D:ℝ)+1/(D:ℝ) := add_le_add hx hy
    _ = _ := by ring
