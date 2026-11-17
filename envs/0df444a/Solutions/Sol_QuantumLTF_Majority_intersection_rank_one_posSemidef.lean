-- Prove2me | solution 1 for QuantumLTF.Majority.intersection_rank_one_posSemidef
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T00:48:41.556569+00:00
-- url     : https://prove2.me/submissions/e6a9eb27-5d25-4396-801d-25f0a445f355

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n r : ℕ, ∀ W : Fin (r+1) → ℝ, ∀ S : Qubits n,
    Matrix.PosSemidef (fun A B : ExactSupports n r =>
      (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)) := by
  classical
  intro n r W S
  let v : ExactSupports n r → ℝ := fun A => W (intersectionIndex A S)
  have hv : Matrix.PosSemidef (Matrix.vecMulVec v (star v)) :=
    Matrix.posSemidef_vecMulVec_self_star v
  have hc : 0 ≤ (2 : ℝ) ^ (-n : ℤ) := by positivity
  have hs := hv.smul hc
  have hmat :
      (fun A B : ExactSupports n r =>
        (2:ℝ)^(-n:ℤ) * W (intersectionIndex A S) * W (intersectionIndex B S)) =
        (2 : ℝ) ^ (-n : ℤ) • Matrix.vecMulVec v (star v) := by
    ext A B
    simp [Matrix.vecMulVec, v]
    ring
  rw [hmat]
  exact hs

