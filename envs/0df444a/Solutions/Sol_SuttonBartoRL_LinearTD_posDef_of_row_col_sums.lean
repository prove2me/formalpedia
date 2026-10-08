-- Prove2me | solution 1 for SuttonBartoRL.LinearTD.posDef_of_row_col_sums
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T13:51:09.018315+00:00
-- url     : https://prove2.me/submissions/c2260f9b-2c52-441b-826c-38ed1bc5e5b8

import Mathlib
import Definitions.Def_SuttonBartoRL_LinearTD_MDP
import Definitions.Def_SuttonBartoRL_LinearTD_LinearTD

open Matrix

open SuttonBartoRL.LinearTD in
theorem solution {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℝ)
    (hdiag : ∀ i, 0 < M i i) (hoff : ∀ i j, i ≠ j → M i j ≤ 0)
    (hrow : ∀ i, 0 < ∑ j, M i j) (hcol : ∀ j, 0 ≤ ∑ i, M i j) :
    IsPosDefNonsym M := by
  intro y hy
  have key : ∀ i j, M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2 ≤ y i * (M i j * y j) := by
    intro i j
    by_cases h : i = j
    · subst h; nlinarith
    · have := mul_nonpos_of_nonpos_of_nonneg (hoff i j h) (sq_nonneg (y i - y j))
      nlinarith [this]
  have hsum : y ⬝ᵥ (M *ᵥ y) = ∑ i, ∑ j, y i * (M i j * y j) := by
    simp [dotProduct, mulVec, Finset.mul_sum]
  have hlow : ∑ i, ∑ j, (M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2)
      ≤ ∑ i, ∑ j, y i * (M i j * y j) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => key i j
  have hsplit : ∑ i, ∑ j, (M i j * y i ^ 2 / 2 + M i j * y j ^ 2 / 2)
      = (∑ i, y i ^ 2 * ∑ j, M i j) / 2 + (∑ j, y j ^ 2 * ∑ i, M i j) / 2 := by
    simp only [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => M i j * y j ^ 2 / 2)]
    simp only [Finset.sum_div, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  obtain ⟨k, hk⟩ : ∃ k, y k ≠ 0 := by
    by_contra h; push_neg at h; exact hy (funext h)
  have hpos : 0 < ∑ i, y i ^ 2 * ∑ j, M i j := by
    apply Finset.sum_pos' (fun i _ => mul_nonneg (sq_nonneg _) (hrow i).le)
    exact ⟨k, Finset.mem_univ _, mul_pos (by positivity) (hrow k)⟩
  have hnn : 0 ≤ ∑ j, y j ^ 2 * ∑ i, M i j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (hcol j)
  rw [hsum]
  linarith
