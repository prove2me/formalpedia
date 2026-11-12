-- Prove2me | solution 1 for RegAggregation.Posterior.KS1_ge_S2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-20T08:37:46.968723+00:00
-- url     : https://prove2.me/submissions/d4c04fae-5381-4554-a08e-6f44eed6fc7e

import Definitions.Def_RegAggregation_Posterior_Model
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

open scoped BigOperators
open RegAggregation.Posterior

theorem solution (K : ℕ) (μ0 : ℝ) (P : Fin K → ℝ) :
    S2 μ0 P ≤ (K : ℝ) * S1 μ0 P ∧
    ((∃ i k, i ≠ k ∧ P i ≠ P k) → S2 μ0 P < (K : ℝ) * S1 μ0 P) := by
  have hid : (∑ i, ∑ k, (P i - P k) ^ 2) =
      2 * ((K : ℝ) * S1 μ0 P - S2 μ0 P) := by
    have hpoint (i k : Fin K) : (P i - P k) ^ 2 =
        (P i - μ0) ^ 2 + (P k - μ0) ^ 2 -
          2 * ((P k - μ0) * (P i - μ0)) := by ring
    simp_rw [hpoint]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, S1, S2]
    ring
  have hnonneg : 0 ≤ ∑ i, ∑ k, (P i - P k) ^ 2 := by
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun k _ => sq_nonneg _
  constructor
  · linarith
  · rintro ⟨i, k, _, hik⟩
    have hsquare : 0 < (P i - P k) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hik)
    have hinner : (P i - P k) ^ 2 ≤ ∑ j, (P i - P j) ^ 2 := by
      exact Finset.single_le_sum (f := fun j : Fin K => (P i - P j) ^ 2)
        (fun j _ => sq_nonneg (P i - P j)) (Finset.mem_univ k)
    have houter : (∑ j, (P i - P j) ^ 2) ≤ ∑ l, ∑ j, (P l - P j) ^ 2 := by
      exact Finset.single_le_sum (f := fun l : Fin K => ∑ j, (P l - P j) ^ 2)
        (fun l _ => Finset.sum_nonneg fun j _ => sq_nonneg (P l - P j)) (Finset.mem_univ i)
    linarith

#print axioms solution
