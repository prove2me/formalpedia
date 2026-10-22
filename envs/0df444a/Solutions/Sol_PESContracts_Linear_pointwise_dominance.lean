-- Prove2me | solution 1 for PESContracts.Linear.pointwise_dominance
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:16:08.954057+00:00
-- url     : https://prove2.me/submissions/f2d1c447-339a-44a4-91f2-dc79f907dbdc

import Mathlib
import Definitions.Def_PESContracts_Linear_Model
set_option autoImplicit false

open PESContracts.Linear

theorem solution (M : Params) (hM : M.Standing) (k : ℝ) (hk : 0 < k)
    (θ : ℝ) (hθ : θ ∈ Set.Icc 0 1) (a : ℝ) (ha : a ∈ Set.Icc 0 M.a0) :
    k * a - cost M.h (a - θ * M.a0) ≤
      2 * ((k - k / 2) * linAction M (k / 2) θ) := by
  obtain ⟨ha0, hh, -, -, -⟩ := hM
  have hcost0 : 0 ≤ cost M.h (a - θ * M.a0) := by
    unfold cost; split_ifs
    · positivity
    · exact le_rfl
  have e : 2 * ((k - k / 2) * linAction M (k / 2) θ) = k * linAction M (k / 2) θ := by ring
  rw [e]
  unfold linAction
  rw [mul_min_of_nonneg _ _ hk.le]
  apply le_min
  · -- bound by k * (θ a0 + p/h)
    unfold cost
    by_cases hx : 0 ≤ a - θ * M.a0
    · rw [if_pos hx]
      have : k * a - M.h / 2 * (a - θ * M.a0) ^ 2 ≤ k * (θ * M.a0 + k / 2 / M.h) := by
        have h1 : 0 ≤ (M.h * (a - θ * M.a0) - k / 2 * 2 / 2 * 1) ^ 2 := sq_nonneg _
        have key : k * (a - θ * M.a0) - M.h / 2 * (a - θ * M.a0) ^ 2 ≤ k * (k / 2 / M.h) := by
          rw [← sub_nonneg]
          have : k * (k / 2 / M.h) - (k * (a - θ * M.a0) - M.h / 2 * (a - θ * M.a0) ^ 2)
              = (M.h * (a - θ * M.a0) - k) ^ 2 / (2 * M.h) := by
            field_simp; ring
          rw [this]; positivity
        nlinarith [key]
      exact this
    · rw [if_neg hx]
      push_neg at hx
      have : 0 < k / 2 / M.h := by positivity
      nlinarith [mul_pos hk this]
  · have : k * a ≤ k * M.a0 := mul_le_mul_of_nonneg_left ha.2 hk.le
    linarith
