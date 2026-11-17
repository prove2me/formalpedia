-- Prove2me | solution 1 for QuantumLTF.Majority.sum_by_intersectionIndex
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:51:24.364193+00:00
-- url     : https://prove2.me/submissions/34d7cc73-9155-4bf0-a14b-914bdf7f5421

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_intersectionIndex_fiber_card

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, r ≤ n → ∀ A : ExactSupports n r,
    ∀ f : Fin (r+1) → ℝ,
    ∑ S : Qubits n, f (intersectionIndex A S) =
      (2^(n-r) : ℝ) * ∑ a : Fin (r+1), (r.choose a : ℝ) * f a := by
  classical
  intro n r hrn A f
  rw [← Finset.sum_fiberwise' (Finset.univ : Finset (Qubits n))
    (intersectionIndex A) f]
  simp_rw [Finset.sum_const, nsmul_eq_mul]
  simp_rw [intersectionIndex_fiber_card n r hrn A]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  norm_num
  ring

