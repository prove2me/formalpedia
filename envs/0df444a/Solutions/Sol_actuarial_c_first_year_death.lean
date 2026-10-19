-- Prove2me | solution 1 for actuarial_c_first_year_death
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T15:01:28.250502+00:00
-- url     : https://prove2.me/submissions/2fac61ee-b899-41e7-8fc9-9a55341504ab

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

theorem solution (h : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hh : 0 < h) (hp : p 0 = 1) (hz : ∀ j, 0 < j → p j = 0) : epv h v b p=v*b 0 := by
  rw [actH_epv, Finset.sum_eq_single 0]
  · simp [hp]
  · intro j _ hj; rw [hz j (Nat.pos_of_ne_zero hj), mul_zero]
  · intro h0; exact absurd (Finset.mem_range.mpr hh) h0

