-- Prove2me | solution 1 for Sendov.centroid_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T19:15:54.873622+00:00
-- url     : https://prove2.me/submissions/a87d1ef2-880b-4a31-9edf-1e810525687c

import Definitions.Def_Sendov_Counterexample_Factor
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_Sendov_Counterexample_Identities
import Theorems.Thm_Sendov_prod_cons_eq

set_option autoImplicit false
open Sendov
open Polynomial Multiset
variable {n : ℕ} {a c : ℂ} {z q : Multiset ℂ} {p : ℂ[X]}
namespace Sendov
theorem _root_.solution (hn : 2 ≤ n) {p : ℂ[X]} (hc0 : c ≠ 0)
    (hzcard : z.card = n - 1) (hqcard : q.card = n - 1)
    (hpz : p = C c * ((X - C a) * (z.map (fun w => X - C w)).prod))
    (hpq : derivative p
      = C ((n : ℂ) * c) * ((q.map (fun v => a - v⁻¹)).map (fun w => X - C w)).prod) :
    ((n : ℂ) - 1) * (a + z.sum) = (n : ℂ) * (q.map (fun v => a - v⁻¹)).sum := by
  have hcard1 : (a ::ₘ z).card = n := by
    simp only [Multiset.card_cons, hzcard]
    omega
  have hcard2 : (q.map (fun v => a - v⁻¹)).card = n - 1 := by
    rw [Multiset.card_map, hqcard]
  -- the coefficient of `X^{n-1}` in `p`
  have hp1 : p.coeff (n - 1) = c * (-(a + z.sum)) := by
    rw [hpz, prod_cons_eq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (a ::ₘ z) (by rw [hcard1]; omega)
    rw [hcard1] at this
    rw [this, Multiset.sum_cons]
  -- the coefficient of `X^{n-2}` in `p'`
  have hp2 : (derivative p).coeff (n - 2)
      = (n : ℂ) * c * (-((q.map (fun v => a - v⁻¹)).sum)) := by
    rw [hpq, coeff_C_mul]
    congr 1
    have := multiset_prod_X_sub_C_coeff_card_pred (q.map (fun v => a - v⁻¹))
      (by rw [hcard2]; omega)
    rw [hcard2] at this
    have hn2 : n - 1 - 1 = n - 2 := by omega
    rwa [hn2] at this
  -- and `p'.coeff (n-2) = (n-1) p.coeff (n-1)`
  have hlink : (derivative p).coeff (n - 2) = p.coeff (n - 1) * ((n : ℂ) - 1) := by
    have hsucc : n - 2 + 1 = n - 1 := by omega
    have h1 : ((n - 2 : ℕ) : ℂ) + 1 = (n : ℂ) - 1 := by
      have h2 : (2 : ℕ) ≤ n := hn
      push_cast [Nat.cast_sub h2]
      ring
    rw [coeff_derivative, hsucc, h1]
  rw [hp1, hp2] at hlink
  refine mul_left_cancel₀ hc0 ?_
  linear_combination hlink
end Sendov
