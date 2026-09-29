-- Prove2me | solution 1 for Polynomial.eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2e11983c-c782-5d3d-92a7-df10c0202490

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible

set_option autoImplicit false

open Polynomial

theorem solution
    (t n : ℤ) (P : Polynomial ℚ)
    (hirr : Irreducible (X ^ 2 + C (t : ℚ) * X + C (n : ℚ) : Polynomial ℚ))
    (hP : P.natDegree ≤ 4)
    (hPQ : P * P.comp (-X - C (t : ℚ)) = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 4)
    (hpos : ∃ m : ℤ, 0 < P.eval (m : ℚ)) :
    P = (X ^ 2 + C (t : ℚ) * X + C (n : ℚ)) ^ 2 := by

  set N : Polynomial ℚ := X ^ 2 + C (t : ℚ) * X + C (n : ℚ) with hN
  have hNdeg : N.natDegree = 2 := by rw [hN]; compute_degree!
  have hN0 : N ≠ 0 := fun h => by rw [h, natDegree_zero] at hNdeg; exact absurd hNdeg (by decide)
  have hNcomp : N.comp (-X - C (t : ℚ)) = N := by
    rw [hN]
    simp only [add_comp, mul_comp, pow_comp, X_comp, C_comp]
    ring

  have hprime : Prime N := UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
  have hdvd : P ∣ N ^ 4 := ⟨_, hPQ.symm⟩
  obtain ⟨a, ha, w, hw⟩ := (dvd_prime_pow hprime 4).mp hdvd

  obtain ⟨c, hc, hcw⟩ := Polynomial.isUnit_iff.mp w.isUnit
  obtain ⟨c, rfl⟩ := hc
  have hPu : P = C ((c⁻¹ : ℚˣ) : ℚ) * N ^ a := by
    have h1 : P * C (c : ℚ) = N ^ a := by rw [hcw]; exact hw
    calc P = P * C (c : ℚ) * C ((c⁻¹ : ℚˣ) : ℚ) := by
          rw [mul_assoc, ← C_mul, Units.mul_inv, C_1, mul_one]
      _ = C ((c⁻¹ : ℚˣ) : ℚ) * N ^ a := by rw [h1, mul_comm]
  set u : ℚ := ((c⁻¹ : ℚˣ) : ℚ) with hu
  have hu0 : u ≠ 0 := (c⁻¹).ne_zero

  have hprod : C (u * u) * N ^ (a + a) = N ^ 4 := by
    rw [← hPQ, hPu, mul_comp, C_comp, pow_comp, hNcomp, C_mul, pow_add]
    ring

  have ha2 : a = 2 := by
    have h := congrArg Polynomial.natDegree hprod
    rw [natDegree_C_mul (mul_ne_zero hu0 hu0), natDegree_pow, natDegree_pow, hNdeg] at h
    omega

  have huu : u * u = 1 := by
    rw [ha2, show 2 + 2 = 4 from rfl] at hprod
    have h : C (u * u) * N ^ 4 = C 1 * N ^ 4 := by rw [hprod, C_1, one_mul]
    exact C_inj.mp (mul_right_cancel₀ (pow_ne_zero 4 hN0) h)

  rcases mul_self_eq_one_iff.mp huu with h1 | h1
  · rw [hPu, h1, C_1, one_mul, ha2]
  · exfalso
    obtain ⟨m, hm⟩ := hpos
    rw [hPu, h1, ha2, eval_mul, eval_C, eval_pow] at hm
    nlinarith [sq_nonneg (N.eval (m : ℚ))]

end S_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible
end P2MW
export P2MW.S_Polynomial_eq_sq_of_mul_comp_neg_X_sub_C_eq_pow_four_of_irreducible (solution)
