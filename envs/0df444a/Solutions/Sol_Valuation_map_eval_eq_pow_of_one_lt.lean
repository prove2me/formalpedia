-- Prove2me | solution 1 for Valuation.map_eval_eq_pow_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.503601+00:00
-- url     : https://prove2.me/submissions/6c8949c0-4915-5be9-9033-04a62ce263c1

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Algebra.Polynomial.Eval.Degree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Valuation_map_eval_eq_pow_of_one_lt

set_option autoImplicit false

theorem solution {R : Type*} [CommRing R]
    {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)
    {f : Polynomial R} {x : R} (hc : ∀ i, v (f.coeff i) ≤ 1) (hl : v f.leadingCoeff = 1)
    (hx : 1 < v x) : v (f.eval x) = v x ^ f.natDegree := by
  have hx0 : v x ≠ 0 := (zero_lt_one.trans hx).ne'
  have hl' : v (f.coeff f.natDegree) = 1 := hl
  have htop : v (f.coeff f.natDegree * x ^ f.natDegree) = v x ^ f.natDegree := by
    rw [map_mul, map_pow, hl', one_mul]
  have hlower : v (∑ i ∈ Finset.range f.natDegree, f.coeff i * x ^ i)
      < v x ^ f.natDegree := by
    refine v.map_sum_lt (pow_ne_zero _ hx0) ?_
    intro i hi
    rw [Finset.mem_range] at hi
    rw [map_mul, map_pow]
    calc v (f.coeff i) * v x ^ i ≤ 1 * v x ^ i := mul_le_mul' (hc i) le_rfl
      _ = v x ^ i := one_mul _
      _ < v x ^ f.natDegree := pow_lt_pow_right₀ hx hi
  rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ,
    Valuation.map_add_eq_of_lt_right _ (htop ▸ hlower), htop]

end S_Valuation_map_eval_eq_pow_of_one_lt
end P2MW
export P2MW.S_Valuation_map_eval_eq_pow_of_one_lt (solution)
