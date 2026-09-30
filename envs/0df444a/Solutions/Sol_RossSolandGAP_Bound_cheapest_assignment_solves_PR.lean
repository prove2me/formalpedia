-- Prove2me | solution 1 for RossSolandGAP.Bound.cheapest_assignment_solves_PR
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-30T05:04:28.520256+00:00
-- url     : https://prove2.me/submissions/e9a5507c-5a82-451e-8de3-4c7aac8f8796

import Mathlib
import Definitions.Def_RossSolandGAP_Bound_Model

open Finset


open RossSolandGAP.Bound

theorem solution {m n : ℕ} (c : Fin m → Fin n → ℝ) (a : Fin n → Fin m)
    (ha : IsCheapest c a) :
    FeasiblePR (xPR a) ∧ cost c (xPR a) = Z c a ∧
    (∀ x, FeasiblePR x → Z c a ≤ cost c x) ∧
    (∀ (r : Fin m → Fin n → ℝ) (b : Fin m → ℝ) (x : Fin m → Fin n → ℝ),
      FeasibleP r b x → Z c a ≤ cost c x) := by
  have hbinary : IsBinary (xPR a) := by
    intro i j
    by_cases h : a j = i
    · right; simp [xPR, h]
    · left; simp [xPR, h]
  have hcol : ∀ j, ∑ i, xPR a i j = 1 := by
    intro j
    simp only [xPR]
    rw [Fintype.sum_ite_eq (a j) (fun _ => (1 : ℝ))]
  have hinner : ∀ j, ∑ i, c i j * (if a j = i then 1 else 0) = c (a j) j := by
    intro j
    trans ∑ i, (if a j = i then c i j else 0)
    · apply Finset.sum_congr rfl
      intro i _
      split <;> simp
    · rw [Fintype.sum_ite_eq]
  have hcost : cost c (xPR a) = Z c a := by
    simp only [cost, Z, xPR]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact hinner j
  have hbound : ∀ x, FeasiblePR x → Z c a ≤ cost c x := by
    intro x hx
    have hx_nn : ∀ i j, 0 ≤ x i j := by
      intro i j
      rcases hx.1 i j with h | h <;> linarith
    calc Z c a = ∑ j, c (a j) j * (∑ i, x i j) := by
          simp only [Z]
          apply Finset.sum_congr rfl
          intro j _
          rw [hx.2 j, mul_one]
      _ = ∑ j, ∑ i, c (a j) j * x i j := by
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.mul_sum]
      _ ≤ ∑ j, ∑ i, c i j * x i j := by
          apply Finset.sum_le_sum
          intro j _
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_right (ha j i) (hx_nn i j)
      _ = cost c x := by
          rw [cost, Finset.sum_comm]
  exact ⟨⟨hbinary, hcol⟩, hcost, hbound, fun r b x hx => hbound x ⟨hx.1, hx.2.2⟩⟩

