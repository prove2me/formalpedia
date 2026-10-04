-- Prove2me | solution 1 for PolylogKServer.Allocation.claim15
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T07:39:16.017578+00:00
-- url     : https://prove2.me/submissions/c75d6aae-8dda-46f4-bc4b-9ae4e6877c84

import Mathlib

open Finset in
theorem solution (d k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (A : Finset (Fin d × Fin k))
    (y y' : Fin d × Fin k → ℝ) (hy'0 : ∀ z, 0 ≤ y' z) (hy'1 : ∀ z, y' z ≤ 1)
    (hA : 1 ≤ ∑ z ∈ A, y' z) (htot : (k : ℝ) * d - k ≤ ∑ z, y' z) :
    ∑ z ∈ A, (y z + ε / (1 + k)) - (1 + ε) * ∑ z ∈ A, y' z ≤
      ∑ z ∈ A, y z - ∑ z ∈ A, y' z := by
  set S := ∑ z ∈ A, y' z with hS
  have hsplit : ∑ z ∈ Aᶜ, y' z + S = ∑ z, y' z := by
    rw [hS, add_comm]; exact Finset.sum_add_sum_compl A y'
  have hcomp : ∑ z ∈ Aᶜ, y' z ≤ (Aᶜ.card : ℝ) := by
    calc ∑ z ∈ Aᶜ, y' z ≤ ∑ z ∈ Aᶜ, (1 : ℝ) := Finset.sum_le_sum (fun z _ => hy'1 z)
      _ = (Aᶜ.card : ℝ) := by simp
  have hcard : (Aᶜ.card : ℝ) = (k : ℝ) * d - A.card := by
    rw [Finset.card_compl]
    have h1 : A.card ≤ Fintype.card (Fin d × Fin k) := Finset.card_le_univ A
    rw [Nat.cast_sub h1]
    simp [Fintype.card_prod, Fintype.card_fin, mul_comm]
  have hlow : (A.card : ℝ) - k ≤ S := by linarith
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hkey : (A.card : ℝ) ≤ (1 + k) * S := by nlinarith
  have hpos : (0 : ℝ) < 1 + k := by linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have : (A.card : ℝ) * (ε / (1 + k)) ≤ ε * S := by
    rw [mul_div_assoc', div_le_iff₀ hpos]
    nlinarith
  linarith
