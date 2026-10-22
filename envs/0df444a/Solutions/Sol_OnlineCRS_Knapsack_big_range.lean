-- Prove2me | solution 1 for OnlineCRS.Knapsack.big_range
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T12:52:22.147998+00:00
-- url     : https://prove2.me/submissions/cb2e3c36-840f-41ac-99a2-3816523643d4

import Mathlib
import Definitions.Def_OnlineCRS_Knapsack_Model

set_option autoImplicit false
open scoped Pointwise
open OnlineCRS.Knapsack

theorem solution {α : Type} [Fintype α] [DecidableEq α]
    (s : α → ℝ) (hs : ∀ e, 0 ≤ s e ∧ s e ≤ 1)
    (b : ℝ) (hb0 : 0 ≤ b) (hb : b ≤ 1 / 2)
    (x : α → ℝ) (hx : x ∈ b • knapsackPolytope s) :
    0 ≤ bigLoad s x ∧ bigLoad s x ≤ b ∧
      0 ≤ bigProbability s b x ∧ bigProbability s b x ≤ 1 := by
  obtain ⟨y, ⟨hy01, hysum⟩, rfl⟩ := Set.mem_smul_set.mp hx
  set L : ℝ := ∑ e ∈ bigElements s, s e * y e with hL
  have hterm : ∀ e, 0 ≤ s e * y e := fun e => mul_nonneg (hs e).1 (hy01 e).1
  have hL0 : 0 ≤ L := Finset.sum_nonneg (fun e _ => hterm e)
  have hL1 : L ≤ 1 := by
    calc L ≤ ∑ e, s e * y e :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun e _ _ => hterm e)
      _ ≤ 1 := hysum
  have hload : bigLoad s (b • y) = b * L := by
    unfold bigLoad
    rw [hL, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e _
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hbL0 : 0 ≤ b * L := mul_nonneg hb0 hL0
  have hbL1 : b * L ≤ b := by nlinarith
  refine ⟨by rw [hload]; exact hbL0, by rw [hload]; exact hbL1, ?_, ?_⟩
  · unfold bigProbability
    rw [hload]
    apply div_nonneg <;> linarith
  · unfold bigProbability
    rw [hload, div_le_one (by linarith)]
    nlinarith

