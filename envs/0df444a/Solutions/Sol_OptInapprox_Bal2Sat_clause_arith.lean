-- Prove2me | solution 1 for OptInapprox.Bal2Sat.clause_arith
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:00:35.417674+00:00
-- url     : https://prove2.me/submissions/6683ae36-0db6-447e-850c-fa181823736e

import Mathlib
import Definitions.Def_OptInapprox_Bal2Sat_Setting

set_option autoImplicit false
open OptInapprox.Bal2Sat

theorem solution :
    (∀ y z : ℝ, (y = 1 ∨ y = -1) → (z = 1 ∨ z = -1) →
      (if y = -1 ∨ z = -1 then (1 : ℝ) else 0) = 3 / 4 - 1 / 4 * y - 1 / 4 * z - 1 / 4 * (y * z)) ∧
    ∀ {n : ℕ} (I : Instance n) (x : Fin n → Bool),
      satWeight I x = ∑ c, I.w c *
        (3 / 4 - 1 / 4 * litVal (I.clause c).1 x - 1 / 4 * litVal (I.clause c).2 x
          - 1 / 4 * (litVal (I.clause c).1 x * litVal (I.clause c).2 x)) := by
  have key : ∀ y z : ℝ, (y = 1 ∨ y = -1) → (z = 1 ∨ z = -1) →
      (if y = -1 ∨ z = -1 then (1 : ℝ) else 0) = 3 / 4 - 1 / 4 * y - 1 / 4 * z - 1 / 4 * (y * z) := by
    intro y z hy hz
    rcases hy with rfl | rfl <;> rcases hz with rfl | rfl <;> norm_num
  refine ⟨key, ?_⟩
  intro n I x
  unfold satWeight
  refine Finset.sum_congr rfl (fun c _ => ?_)
  congr 1
  have hv : ∀ l : Literal n, litVal l x = 1 ∨ litVal l x = -1 := by
    rintro ⟨i, r⟩
    cases r <;> cases h : x i <;> simp [litVal, OptInapprox.MaxCut.pm, h]
  have ht : ∀ l : Literal n, litTrue l x = true ↔ litVal l x = -1 := by
    rintro ⟨i, r⟩
    cases r <;> cases h : x i <;> simp [litTrue, litVal, OptInapprox.MaxCut.pm, h] <;> norm_num
  rw [← key _ _ (hv _) (hv _)]
  simp only [clauseSat, Bool.or_eq_true, ht]
