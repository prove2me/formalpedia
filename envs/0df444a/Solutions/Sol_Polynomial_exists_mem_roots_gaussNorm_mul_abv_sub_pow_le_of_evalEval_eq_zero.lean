-- Prove2me | solution 1 for Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/dd93b3cc-6c40-5a57-8afb-9e130e2ce785

import Mathlib
import Theorems.Thm_Polynomial_abv_eval_le_gaussNorm
import Theorems.Thm_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero

set_option autoImplicit false

open Polynomial
open scoped Polynomial.Bivariate

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] (v : AbsoluteValue K ℝ) (hv : IsNonarchimedean v)
    (H : K[X][Y]) {B : ℝ} (hB : ∀ j, (H.coeff j).gaussNorm v 1 ≤ B)
    {y w : K} (hy : v y ≤ 1) (hH : H.evalEval y w = 0)
    (hlt : B * v w < (H.eval 0).gaussNorm v 1) :
    ∃ a ∈ (H.eval 0).roots, v a ≤ 1 ∧
      (H.eval 0).gaussNorm v 1 * v (y - a) ^ (H.eval 0).natDegree ≤ B * v w := by
  have hP : H.eval 0 = H.coeff 0 := (Polynomial.coeff_zero_eq_eval_zero H).symm
  rw [hP] at hlt ⊢
  have hB0 : 0 ≤ B := (Polynomial.gaussNorm_nonneg v (H.coeff 0) zero_le_one).trans (hB 0)

  have hw : v w ≤ 1 := by
    by_contra h
    have h1 : B * 1 ≤ B * v w := mul_le_mul_of_nonneg_left (not_le.1 h).le hB0
    have h2 := hlt.trans_le (hB 0)
    rw [mul_one] at h1
    exact absurd (h1.trans_lt h2) (lt_irrefl B)

  have hsum : ∑ j ∈ Finset.range (H.natDegree + 1), (H.coeff j).eval y * w ^ j = 0 := by
    have := hH
    rw [Polynomial.evalEval, Polynomial.eval_eq_sum_range (p := H) (C w),
      Polynomial.eval_finsetSum] at this
    simpa only [eval_mul, eval_pow, eval_C] using this

  rw [Finset.sum_range_succ', pow_zero, mul_one] at hsum
  have hPy : (H.coeff 0).eval y
      = -∑ j ∈ Finset.range H.natDegree, (H.coeff (j + 1)).eval y * w ^ (j + 1) :=
    eq_neg_of_add_eq_zero_right hsum

  have hbound : v ((H.coeff 0).eval y) ≤ B * v w := by
    rw [hPy, v.map_neg]
    refine Finset.sum_induction _ (fun x => v x ≤ B * v w) ?_ ?_ ?_
    · intro a b ha hb
      exact (hv a b).trans (max_le ha hb)
    · simpa using mul_nonneg hB0 (v.nonneg w)
    · intro j _
      rw [v.map_mul, v.map_pow]
      have h1 : v ((H.coeff (j + 1)).eval y) ≤ B :=
        (Polynomial.abv_eval_le_gaussNorm v hv zero_le_one _ hy).trans (hB (j + 1))
      have h2 : v w ^ (j + 1) ≤ v w := pow_le_of_le_one (v.nonneg w) hw (Nat.succ_ne_zero j)
      exact mul_le_mul h1 h2 (pow_nonneg (v.nonneg w) _) hB0

  obtain ⟨a, ha, ha1, hle⟩ :=
    Polynomial.exists_mem_roots_gaussNorm_mul_abv_sub_pow_le v hv (H.coeff 0) hy
      (hbound.trans_lt hlt)
  exact ⟨a, ha, ha1, hle.trans hbound⟩

end S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero
end P2MW
export P2MW.S_Polynomial_exists_mem_roots_gaussNorm_mul_abv_sub_pow_le_of_evalEval_eq_zero (solution)
