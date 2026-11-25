-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.le_monoNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:37:16.228916+00:00
-- url     : https://prove2.me/submissions/8e5e4f7a-a05e-4173-bd81-e9efb620e21e

import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_MonoNormSq
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_SphericalMonomials_ChiPSt
import Theorems.Thm_ReciprocityTheory_GeometryOfNumbersTheory_factorial_sum_add_le
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.GeometryOfNumbersTheory
open Finset
private theorem inv_le_mul_div_of_le_mul {Q A E F : ℝ} (hF : 0 < F) (hA : 0 < A) (hE : 1 ≤ E) (hQ : 0 ≤ Q)
    (h : F ≤ Q * A) : Q⁻¹ ≤ A * E / F := by
  rcases hQ.eq_or_lt with h0 | h0
  · rw [← h0, inv_zero]
    exact div_nonneg (mul_nonneg hA.le (by linarith)) hF.le
  · have key : Q⁻¹ * F ≤ A * E := by
      calc Q⁻¹ * F ≤ Q⁻¹ * (Q * A) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hQ)
        _ = A := by rw [← mul_assoc, inv_mul_cancel₀ h0.ne', one_mul]
        _ ≤ A * E := le_mul_of_one_le_right hA.le hE
    first
      | exact (le_div_iff₀ hF).mpr key
      | exact (le_div_iff hF).mpr key
end ReciprocityTheory.GeometryOfNumbersTheory
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Finset
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {D : ℕ} (a : Fin (D + 1) → ℕ) :
    (((D + 1 : ℝ) ^ (∑ i, a i)) * ((∑ i, a i : ℕ) + D : ℝ) ^ D)⁻¹ ≤ monoNormSq a := by
  unfold monoNormSq
  apply inv_le_mul_div_of_le_mul (by exact_mod_cast Nat.factorial_pos _)
    (by exact_mod_cast (Finset.prod_pos fun i _ => Nat.factorial_pos (a i)))
    (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero D)) (by positivity)
  exact_mod_cast factorial_sum_add_le a
end ReciprocityTheory.GeometryOfNumbersTheory
