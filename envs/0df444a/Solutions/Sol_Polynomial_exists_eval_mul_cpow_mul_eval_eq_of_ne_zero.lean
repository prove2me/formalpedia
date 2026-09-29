-- Prove2me | solution 1 for Polynomial.exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/2fdcb68f-6bd2-5721-9435-96af09d499d6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero

set_option autoImplicit false

open Polynomial

namespace GammaRat

theorem eval_inv_eq_eval_reverse_mul_pow (f : Polynomial ℂ) (Y : ℂ) (hY : Y ≠ 0) :
    f.eval Y⁻¹ = f.reverse.eval Y * Y ^ (-(f.natDegree : ℤ)) := by
  haveI : Invertible Y⁻¹ := invertibleOfNonzero (inv_ne_zero hY)
  have h := Polynomial.eval₂_reverse_mul_pow (RingHom.id ℂ) Y⁻¹ f
  simp only [Polynomial.eval₂_id] at h
  rw [invOf_eq_inv, inv_inv] at h
  rw [← h, zpow_neg, zpow_natCast, inv_pow]

end GammaRat

theorem solution
    (q : ℂ) (hq : q ≠ 0) (P Pd Q Qd : Polynomial ℂ) (m md : ℤ) (hP : P ≠ 0) (hQd : Qd ≠ 0) :
    ∃ (R₁ R₂ : Polynomial ℂ) (r : ℤ), R₂ ≠ 0 ∧
      ∀ s : ℂ,
        R₂.eval (q ^ s) * (q ^ ((md : ℂ) * s) * Pd.eval (q ^ (-s))) * Q.eval (q ^ s) =
          (R₁.eval (q ^ s) * q ^ ((r : ℂ) * s)) * (q ^ ((m : ℂ) * (-s)) * P.eval (q ^ s)) * Qd.eval (q ^ (-s)) := by
  refine ⟨Q * Pd.reverse, P * Qd.reverse, md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ),
    mul_ne_zero hP (by rwa [Ne, Polynomial.reverse_eq_zero]), fun s => ?_⟩
  set Y : ℂ := q ^ s with hY
  have hY0 : Y ≠ 0 := by
    rw [hY]; exact fun h => hq ((Complex.cpow_eq_zero_iff q s).mp h).1
  have hX : q ^ (-s) = Y⁻¹ := by rw [hY, Complex.cpow_neg]
  have h1 : q ^ ((md : ℂ) * s) = Y ^ md := by rw [hY, Complex.cpow_int_mul]
  have h2 : q ^ ((m : ℂ) * (-s)) = Y ^ (-m) := by
    rw [hY, ← Complex.cpow_int_mul, Int.cast_neg]; ring_nf
  have h3 : q ^ (((md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ) : ℤ) : ℂ) * s)
      = Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) := by rw [hY, Complex.cpow_int_mul]
  rw [hX, h1, h2, h3, Polynomial.eval_mul, Polynomial.eval_mul,
    GammaRat.eval_inv_eq_eval_reverse_mul_pow Pd Y hY0, GammaRat.eval_inv_eq_eval_reverse_mul_pow Qd Y hY0]

  have hz : Y ^ md * Y ^ (-(Pd.natDegree : ℤ)) =
      Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) * Y ^ (-m) * Y ^ (-(Qd.natDegree : ℤ)) := by
    rw [← zpow_add₀ hY0, ← zpow_add₀ hY0, ← zpow_add₀ hY0]; congr 1; ring
  calc (P.eval Y * Qd.reverse.eval Y) * (Y ^ md * (Pd.reverse.eval Y * Y ^ (-(Pd.natDegree : ℤ)))) * Q.eval Y
      = (P.eval Y * Qd.reverse.eval Y * Pd.reverse.eval Y * Q.eval Y) * (Y ^ md * Y ^ (-(Pd.natDegree : ℤ))) := by
        ring
    _ = (P.eval Y * Qd.reverse.eval Y * Pd.reverse.eval Y * Q.eval Y) *
          (Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) * Y ^ (-m) * Y ^ (-(Qd.natDegree : ℤ))) := by
        rw [hz]
    _ = (Q.eval Y * Pd.reverse.eval Y) * Y ^ (md + m + (Qd.natDegree : ℤ) - (Pd.natDegree : ℤ)) *
          (Y ^ (-m) * P.eval Y) * (Qd.reverse.eval Y * Y ^ (-(Qd.natDegree : ℤ))) := by ring

end S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero
end P2MW
export P2MW.S_Polynomial_exists_eval_mul_cpow_mul_eval_eq_of_ne_zero (solution)
