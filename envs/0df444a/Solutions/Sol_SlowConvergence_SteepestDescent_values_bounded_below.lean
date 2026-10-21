-- Prove2me | solution 1 for SlowConvergence.SteepestDescent.values_bounded_below
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T01:40:18.054358+00:00
-- url     : https://prove2.me/submissions/79eb347e-e485-45cb-9b83-908fd825ad55

import Mathlib
import Definitions.Def_SlowConvergence_SteepestDescent_Data

set_option autoImplicit false
open SlowConvergence.SteepestDescent

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (αlo αhi : ℝ) (hlo : 0 < αlo) (hlohi : αlo ≤ αhi) (hhi : αhi < 2)
    (α : ℕ → ℝ) (hα : ∀ k, αlo ≤ α k ∧ α k ≤ αhi) :
    (∀ k : ℕ, fk τ α k - fk τ α (k + 1) ≤ 1 / 2 * (1 / ((k : ℝ) + 1)) ^ (1 + 2 * SlowConvergence.Newton.eta τ)) ∧
      ∀ k : ℕ, 0 ≤ fk τ α k := by
  set t : ℝ := 1 + 2 * SlowConvergence.Newton.eta τ with ht
  have hη : 0 < SlowConvergence.Newton.eta τ := by
    unfold SlowConvergence.Newton.eta
    apply div_pos hτ0; linarith
  have ht1 : 1 < t := by rw [ht]; linarith
  set c : ℕ → ℝ := fun n => (1 / ((n : ℝ) + 1)) ^ t with hc
  have hc0 : ∀ n, 0 ≤ c n := fun n => Real.rpow_nonneg (by positivity) _
  have hdiff : ∀ k, fk τ α k - fk τ α (k + 1) = α k * (1 - 1 / 2 * α k) * c k := by
    intro k; simp [fk, hc, ht]
  have hbd : ∀ k, α k * (1 - 1 / 2 * α k) * c k ≤ 1 / 2 * c k := by
    intro k
    have : α k * (1 - 1 / 2 * α k) ≤ 1 / 2 := by nlinarith [sq_nonneg (α k - 1)]
    exact mul_le_mul_of_nonneg_right this (hc0 k)
  have hsum : Summable c := by
    have h1 : Summable (fun n : ℕ => 1 / (n : ℝ) ^ t) := Real.summable_one_div_nat_rpow.mpr ht1
    have h2 := (summable_nat_add_iff 1).mpr h1
    refine h2.congr (fun n => ?_)
    simp [hc]
    push_cast
    rw [Real.inv_rpow (by positivity)]
  refine ⟨fun k => by rw [hdiff]; exact hbd k, fun k => ?_⟩
  have hform : ∀ k, fk τ α k = fk τ α 0 - ∑ j ∈ Finset.range k, α j * (1 - 1 / 2 * α j) * c j := by
    intro k
    induction k with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have := hdiff n
      linarith
  have hf0 : fk τ α 0 = 1 / 2 * ∑' n, c n := by
    simp [fk, SlowConvergence.Newton.zetaR, hc, ht]
  have hps : ∑ j ∈ Finset.range k, c j ≤ ∑' n, c n := hsum.sum_le_tsum _ (fun j _ => hc0 j)
  have : ∑ j ∈ Finset.range k, α j * (1 - 1 / 2 * α j) * c j ≤ ∑ j ∈ Finset.range k, 1 / 2 * c j :=
    Finset.sum_le_sum (fun j _ => hbd j)
  rw [← Finset.mul_sum] at this
  rw [hform k, hf0]
  linarith
