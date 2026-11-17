-- Prove2me | solution 1 for QuantumLTF.Majority.exact_support_krawtchouk_cost
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:42:53.103196+00:00
-- url     : https://prove2.me/submissions/2379a685-0d18-4d54-9922-56911e79b9f4

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel
import Theorems.Thm_QuantumLTF_Majority_normalized_intersection_sum
import Theorems.Thm_QuantumLTF_Majority_intersectionTransform_parseval_of_cross_zero

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, r ≤ n → ∀ p q : Fin (r+1) → ℝ,
    (∑ t : Fin (r+1), (r.choose t : ℝ) *
      ((-1 : ℝ) ^ (t : ℕ) * p t * q t)) = 0 →
    ∀ T : ℝ, (∑ t : Fin (r+1), (r.choose t : ℝ) *
      (p t^2 + q t^2)) ≤ T →
    let W := intersectionTransform r p q
    let X : Qubits n → Matrix (ExactSupports n r) (ExactSupports n r) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) *
        W (intersectionIndex B S)
    DualCostAtMost X T := by
  classical
  intro n r hrn p q hcross T henergy
  dsimp only
  intro A
  let W := intersectionTransform r p q
  calc
    (∑ S : Qubits n, (2 : ℝ) ^ (-n : ℤ) *
        W (intersectionIndex A S) * W (intersectionIndex A S)) =
      (2 : ℝ) ^ (-n : ℤ) *
        ∑ S : Qubits n, (W (intersectionIndex A S)) ^ 2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro S hS
          ring
    _ = (1 / (2 : ℝ) ^ r) *
        ∑ a : Fin (r + 1), (r.choose a : ℝ) * (W a) ^ 2 := by
          exact normalized_intersection_sum n r hrn A (fun a => (W a) ^ 2)
    _ = ∑ t : Fin (r + 1), (r.choose t : ℝ) * (p t ^ 2 + q t ^ 2) := by
          exact intersectionTransform_parseval_of_cross_zero r p q hcross
    _ ≤ T := henergy

