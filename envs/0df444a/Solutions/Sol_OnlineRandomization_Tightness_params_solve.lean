-- Prove2me | solution 1 for OnlineRandomization.Tightness.params_solve
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T11:31:56.536978+00:00
-- url     : https://prove2.me/submissions/4c463399-53fb-491d-8743-a5b856c726d7

import Mathlib
import Definitions.Def_OnlineRandomization_Tightness_Model
import Definitions.Def_OnlineRandomization_Tightness_MatesGame

open OnlineRandomization.Tightness in
theorem solution (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (t : ℕ) (ht : 2 ≤ t) :
    β = ((2 * (t : ℝ) - 2) * paramSmall α β t + paramLarge α β t + 1) / (2 * (t : ℝ)) ∧
    α = (1 + (2 * (t : ℝ) - 1) * paramLarge α β t) /
      (2 + (2 * (t : ℝ) - 2) * paramSmall α β t) ∧
    0 < 2 + (2 * (t : ℝ) - 2) * paramSmall α β t ∧
    ∀ m M : ℝ, β = ((2 * (t : ℝ) - 2) * m + M + 1) / (2 * (t : ℝ)) →
      α = (1 + (2 * (t : ℝ) - 1) * M) / (2 + (2 * (t : ℝ) - 2) * m) →
      m = paramSmall α β t ∧ M = paramLarge α β t := by
  have hT : (2 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht
  have hk : (0 : ℝ) < 2 * (t : ℝ) - 2 := by linarith
  have hd : (0 : ℝ) < α + 2 * (t : ℝ) - 1 := by linarith
  have h2T : (0 : ℝ) < 2 * (t : ℝ) := by linarith
  have hkne : (2 * (t : ℝ) - 2) ≠ 0 := ne_of_gt hk
  have hdne : (α + 2 * (t : ℝ) - 1) ≠ 0 := ne_of_gt hd
  have hS : (2 * (t : ℝ) - 2) * paramSmall α β t
      = (1 + (2 * (t : ℝ) - 1) * (2 * (t : ℝ) * β - 1) - 2 * α) / (α + 2 * (t : ℝ) - 1) := by
    unfold paramSmall
    rw [mul_div_assoc', mul_div_mul_left _ _ hkne]
  have hL : paramLarge α β t = (2 * (t : ℝ) * α * β + α - 1) / (α + 2 * (t : ℝ) - 1) := rfl
  have hD : 2 + (2 * (t : ℝ) - 2) * paramSmall α β t
      = 2 * (t : ℝ) * (1 + (2 * (t : ℝ) - 1) * β) / (α + 2 * (t : ℝ) - 1) := by
    rw [hS]
    field_simp
    ring
  have hDpos : 0 < 2 + (2 * (t : ℝ) - 2) * paramSmall α β t := by
    rw [hD]
    apply div_pos _ hd
    have : (0 : ℝ) < (2 * (t : ℝ) - 1) * β := mul_pos (by linarith) hβ
    positivity
  have hE1 : (2 * (t : ℝ) - 2) * paramSmall α β t + paramLarge α β t + 1 = 2 * (t : ℝ) * β := by
    rw [hS, hL]
    field_simp
    ring
  have hN : 1 + (2 * (t : ℝ) - 1) * paramLarge α β t
      = α * (2 + (2 * (t : ℝ) - 2) * paramSmall α β t) := by
    rw [hD, hL]
    field_simp
    ring
  refine ⟨?_, ?_, hDpos, ?_⟩
  · rw [hE1]
    field_simp
  · rw [hN, mul_div_assoc, div_self (ne_of_gt hDpos), mul_one]
  · intro m M h1 h2
    have e1 : (2 * (t : ℝ) - 2) * m + M + 1 = 2 * (t : ℝ) * β := by
      rw [h1]; field_simp
    have hDm : (2 + (2 * (t : ℝ) - 2) * m) ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h2
      exact (ne_of_gt hα) h2
    have e2 : α * (2 + (2 * (t : ℝ) - 2) * m) = 1 + (2 * (t : ℝ) - 1) * M := by
      rw [h2, div_mul_cancel₀ _ hDm]
    -- solve the linear system
    have hm : (2 * (t : ℝ) - 2) * m * (α + 2 * (t : ℝ) - 1)
        = 1 + (2 * (t : ℝ) - 1) * (2 * (t : ℝ) * β - 1) - 2 * α := by
      have hM : M = 2 * (t : ℝ) * β - 1 - (2 * (t : ℝ) - 2) * m := by linear_combination e1
      rw [hM] at e2
      linear_combination e2
    have hmval : m = paramSmall α β t := by
      unfold paramSmall
      rw [eq_div_iff (mul_ne_zero hkne hdne)]
      linear_combination hm
    refine ⟨hmval, ?_⟩
    have hM : M = 2 * (t : ℝ) * β - 1 - (2 * (t : ℝ) - 2) * paramSmall α β t := by
      rw [← hmval]; linear_combination e1
    rw [hM]
    linear_combination -hE1
