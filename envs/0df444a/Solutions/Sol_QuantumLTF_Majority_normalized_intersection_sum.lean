-- Prove2me | solution 1 for QuantumLTF.Majority.normalized_intersection_sum
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:50:51.267138+00:00
-- url     : https://prove2.me/submissions/a65f7fff-d4d2-4a00-8c11-4ebeb7a07f63

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_sum_by_intersectionIndex

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r,
    ∀ f : Fin (r+1) → ℝ,
    (2 : ℝ)^(-n : ℤ) * ∑ S : Qubits n, f (intersectionIndex A S) =
      (1/(2:ℝ)^r) * ∑ a : Fin (r+1), (r.choose a : ℝ) * f a := by
  intro n r hrn A f
  rw [sum_by_intersectionIndex n r hrn A f]
  have hpow :
      (2 : ℝ) ^ (-n : ℤ) * (2 ^ (n - r) : ℝ) = 1 / (2 : ℝ) ^ r := by
    rw [zpow_neg, zpow_natCast]
    field_simp
    rw [← pow_add, Nat.sub_add_cancel hrn]
  rw [← mul_assoc, hpow]

