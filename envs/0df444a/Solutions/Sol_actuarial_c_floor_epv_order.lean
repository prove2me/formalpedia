-- Prove2me | solution 1 for actuarial_c_floor_epv_order
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:01:47.158211+00:00
-- url     : https://prove2.me/submissions/06c030ca-2152-42f0-b173-ce321a63f86e

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_death
import Definitions.Def_actuarial_c_path
import Definitions.Def_actuarial_c_epv
import Definitions.Def_actuarial_c_floorBenefit

open ActuarialAssurances



lemma actH_path (h : ℕ) (v : ℝ) (b : ℕ → ℝ) (k : ℕ) :
    path h v b k = if k < h then v^(k+1)*b k else 0 := by
  unfold path death; simp only [mul_ite, mul_one, mul_zero]; rw [Finset.sum_ite_eq]; simp [Finset.mem_range]

lemma actH_epv (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) :
    epv h v b p = ∑ j ∈ Finset.range h, v^(j+1)*b j*p j := by
  unfold epv; rw [Finset.sum_range_succ]; simp only [actH_path, lt_irrefl, if_false, mul_zero, add_zero]
  apply Finset.sum_congr rfl; intro j hj; rw [if_pos (Finset.mem_range.mp hj)]; ring

theorem solution (h : ℕ) (v f : ℝ) (b p : ℕ → ℝ) (hv : 0 ≤ v) (hp : ∀ j, 0 ≤ p j) : epv h v b p ≤ epv h v (floorBenefit f b) p := by
  rw [actH_epv, actH_epv]; apply Finset.sum_le_sum; intro j _
  unfold floorBenefit
  have h1 : 0 ≤ v^(j+1) * p j := mul_nonneg (pow_nonneg hv _) (hp j)
  have h2 : b j ≤ max f (b j) := le_max_right _ _
  nlinarith

