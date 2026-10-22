-- Prove2me | solution 2 for StrictCQ.Scaled.eq_2_4_not_mfcq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:22:40.96597+00:00
-- url     : https://prove2.me/submissions/f76de671-2a82-486e-8bbe-2b68307752dd

import Mathlib
import Definitions.Def_StrictCQ_Scaled_Setting
import Definitions.Def_StrictCQ_Scaled_Conditions

set_option autoImplicit false
open Filter Topology
open scoped InnerProductSpace
open StrictCQ.Scaled

theorem solution {n m p : ℕ} (C : Constraints n m p)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs : xs ∈ C.feasible)
    (l : Fin m → ℝ) (u : Fin p → ℝ) (hu : ∀ j, 0 ≤ u j) (hcomp : ∀ j, C.g j xs ≠ 0 → u j = 0)
    (hnorm : max ‖l‖ ‖u‖ = 1)
    (h24 : ∑ i, l i • gradient (C.h i) xs + ∑ j, u j • gradient (C.g j) xs = 0) :
    ¬ C.MFCQ xs := by
  rintro ⟨hli, d, hd1, hd2⟩
  have hd1' : ∀ i, ⟪d, gradient (C.h i) xs⟫_ℝ = 0 := fun i => by rw [real_inner_comm]; exact hd1 i
  have hd2' : ∀ j, C.g j xs = 0 → ⟪d, gradient (C.g j) xs⟫_ℝ < 0 :=
    fun j hj => by rw [real_inner_comm]; exact hd2 j hj
  -- pair (2.4) with d
  have hpair : ∑ j, u j * ⟪d, gradient (C.g j) xs⟫_ℝ = 0 := by
    have := congrArg (fun w => ⟪d, w⟫_ℝ) h24
    simp only [inner_add_right, inner_sum, inner_smul_right, inner_zero_right, hd1', mul_zero,
      Finset.sum_const_zero, zero_add] at this
    exact this
  -- each term is ≤ 0
  have hterm : ∀ j, u j * ⟪d, gradient (C.g j) xs⟫_ℝ ≤ 0 := by
    intro j
    by_cases hj : C.g j xs = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hu j) (hd2' j hj).le
    · rw [hcomp j hj]; simp
  have hzero : ∀ j, u j * ⟪d, gradient (C.g j) xs⟫_ℝ = 0 := by
    intro j
    exact (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hterm j)).mp hpair j (Finset.mem_univ j)
  have hu0 : ∀ j, u j = 0 := by
    intro j
    by_cases hj : C.g j xs = 0
    · have h1 := hzero j
      have h2 := hd2' j hj
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact absurd h h2.ne
    · exact hcomp j hj
  have hl : ∑ i, l i • gradient (C.h i) xs = 0 := by
    have : ∑ j, u j • gradient (C.g j) xs = 0 := by
      apply Finset.sum_eq_zero; intro j _; rw [hu0 j]; simp
    rw [this, add_zero] at h24
    exact h24
  have hl0 : ∀ i, l i = 0 := by
    intro i
    exact (Fintype.linearIndependent_iff.mp hli) l hl i
  have : max ‖l‖ ‖u‖ = 0 := by
    have h1 : l = 0 := funext hl0
    have h2 : u = 0 := funext hu0
    rw [h1, h2]; simp
  rw [this] at hnorm
  exact zero_ne_one hnorm
