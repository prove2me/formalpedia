-- Prove2me | solution 1 for actuarial_c_discount_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:01:03.656888+00:00
-- url     : https://prove2.me/submissions/bf774356-0281-4517-b534-d7761a1b0c32

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv

open ActuarialAssurances



lemma actH_path (h : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by
  unfold path death; simp only [mul_ite, mul_one, mul_zero]; rw [Finset.sum_ite_eq]; simp [Finset.mem_range]

lemma actH_epv (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    epv h v b p = ∑ j ∈ Finset.range h, v^(j+1)*b j*p j := by
  unfold epv; rw [Finset.sum_range_succ]; simp only [actH_path, lt_irrefl, if_false, mul_zero, add_zero]
  apply Finset.sum_congr rfl; intro j hj; rw [if_pos (Finset.mem_range.mp hj)]; ring

theorem solution (h : ℕ) (v w : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hvw : v ≤ w) (hp : ∀ j, 0 ≤ p j) (hb : ∀ j, 0 ≤ b j) : epv h v b p ≤ epv h w b p := by
  rw [actH_epv, actH_epv]; apply Finset.sum_le_sum; intro j _
  have h1 : v^(j+1) ≤ w^(j+1) := pow_le_pow_left₀ hv hvw _
  have h2 : 0 ≤ b j * p j := mul_nonneg (hb j) (hp j)
  nlinarith

