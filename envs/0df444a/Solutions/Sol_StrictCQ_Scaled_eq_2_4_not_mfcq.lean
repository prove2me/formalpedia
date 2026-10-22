-- Prove2me | solution 1 for StrictCQ.Scaled.eq_2_4_not_mfcq
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:20:04.076041+00:00
-- url     : https://prove2.me/submissions/13d675b4-4597-46ec-a05d-27a6e5319125

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
  have h := congrArg (fun w => ⟪w, d⟫_ℝ) h24
  simp only [inner_add_left, sum_inner, real_inner_smul_left, inner_zero_left, hd1,
    mul_zero, Finset.sum_const_zero, zero_add] at h
  have hle : ∀ j, u j * ⟪gradient (C.g j) xs, d⟫_ℝ ≤ 0 := by
    intro j
    by_cases hj : C.g j xs = 0
    · exact mul_nonpos_of_nonneg_of_nonpos (hu j) (hd2 j hj).le
    · simp [hcomp j hj]
  have hz : ∀ j ∈ Finset.univ, u j * ⟪gradient (C.g j) xs, d⟫_ℝ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun j _ => hle j)).mp h
  have hu0 : ∀ j, u j = 0 := by
    intro j
    by_cases hj : C.g j xs = 0
    · have := hz j (Finset.mem_univ j)
      rcases mul_eq_zero.mp this with h1 | h1
      · exact h1
      · exact absurd h1 (hd2 j hj).ne
    · exact hcomp j hj
  have hu' : u = 0 := funext hu0
  rw [hu'] at h24
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, add_zero] at h24
  have hl0 : ∀ i, l i = 0 := Fintype.linearIndependent_iff.mp hli l h24
  have hl' : l = 0 := funext hl0
  rw [hl', hu'] at hnorm
  simp at hnorm
