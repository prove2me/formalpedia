-- Prove2me | solution 1 for PowerSeries.prime_X_sq_sub_C_X_mul_X_add_C_C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/622827fa-2f53-563e-928f-ec4e1d276408

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C

open Polynomial

set_option autoImplicit false

theorem k3prime_aux
    {D : Type*} [CommRing D] [IsDomain D]
    {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) :
    Irreducible (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) : Polynomial (PowerSeries D)) := by
  set f : Polynomial (PowerSeries D) := Polynomial.X ^ 2 -
      Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X + Polynomial.C (PowerSeries.C c) with hf
  have hf' : f = Polynomial.X ^ 2 + Polynomial.C (-(PowerSeries.X : PowerSeries D)) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) := by
    rw [hf, Polynomial.C_neg]; ring
  have hdeg : f.natDegree = 2 := by
    rw [hf']; compute_degree!
  have hmonic : f.Monic := by
    rw [hf']; monicity!
  by_contra hirr
  obtain ⟨c₁, c₂, h0, h1⟩ := (hmonic.not_irreducible_iff_exists_add_mul_eq_coeff hdeg).mp hirr
  have hc0' : f.coeff 0 = PowerSeries.C c := by
    rw [hf']; simp
  have hc1' : f.coeff 1 = -(PowerSeries.X : PowerSeries D) := by
    rw [hf']; simp
  rw [hc0'] at h0
  rw [hc1'] at h1
  have a0 := congrArg (PowerSeries.coeff 0) h0
  have a1 := congrArg (PowerSeries.coeff 1) h0
  have a2 := congrArg (PowerSeries.coeff 2) h0
  have b0 := congrArg (PowerSeries.coeff 0) h1
  have b1 := congrArg (PowerSeries.coeff 1) h1
  have b2 := congrArg (PowerSeries.coeff 2) h1
  simp only [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.sum_range_succ, Finset.sum_range_zero, zero_add, map_add, map_neg, PowerSeries.coeff_C,
    PowerSeries.coeff_X, if_true] at a0 a1 a2 b0 b1 b2
  norm_num at a0 a1 a2 b0 b1 b2
  set x0 := PowerSeries.constantCoeff c₁ with hx0def
  set x1 := PowerSeries.coeff 1 c₁
  set x2 := PowerSeries.coeff 2 c₁
  set y0 := PowerSeries.constantCoeff c₂ with hy0def
  set y1 := PowerSeries.coeff 1 c₂
  set y2 := PowerSeries.coeff 2 c₂
  have hx0 : x0 ≠ 0 := by
    intro h; apply hc0; rw [a0, h, zero_mul]
  have hy0 : y0 = -x0 := by linear_combination (-1 : D) * b0
  have h21 : 1 + 2 * x1 = 0 := by
    have : x0 * (1 + 2 * x1) = 0 := by
      linear_combination a1 - x0 * b1 + x1 * hy0
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hx0
    · exact h
  have h8 : x0 * (8 * x2) = 1 := by
    linear_combination (4 : D) * a2 - (4 * x0) * b2 + (4 * x2) * hy0 - (4 * x1) * b1 - (2 * x1 + 1) * h21
  have hu : IsUnit x0 := IsUnit.of_mul_eq_one (8 * x2) h8
  apply hcu
  rw [a0, hy0]
  exact hu.mul hu.neg

theorem solution
    {D : Type*} [CommRing D] [IsDomain D] [IsPrincipalIdealRing D]
    {c : D} (hc0 : c ≠ 0) (hcu : ¬IsUnit c) :
    Prime (Polynomial.X ^ 2 - Polynomial.C (PowerSeries.X : PowerSeries D) * Polynomial.X +
      Polynomial.C (PowerSeries.C c) : Polynomial (PowerSeries D)) := by
  haveI : UniqueFactorizationMonoid (PowerSeries D) := inferInstance
  haveI : UniqueFactorizationMonoid (Polynomial (PowerSeries D)) := inferInstance
  exact UniqueFactorizationMonoid.irreducible_iff_prime.mp (k3prime_aux hc0 hcu)

end S_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C
end P2MW
export P2MW.S_PowerSeries_prime_X_sq_sub_C_X_mul_X_add_C_C (solution)
