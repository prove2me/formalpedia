-- Prove2me | solution 1 for QuantumLTF.Majority.bounded_gram_dual_of_moment_identity
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-17T17:38:56.609571+00:00
-- url     : https://prove2.me/submissions/4a3dcaa1-bceb-4b9d-af9e-17388dad5d43

import Mathlib
import Definitions.Def_QuantumLTF_Majority_AdversaryModel

open QAlgorithms
open QuantumLTF.Majority

theorem solution : ∀ n k d : ℕ, ∀ W : ℕ → ℕ → Fin d → ℝ,
    (∀ A B : BoundedSupports n k, A ≠ B →
      (∑ S : Qubits n, if majorityBit A.1 S ≠ majorityBit B.1 S then
        (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
          W A.1.card ((A.1.filter fun i => S i).card) j *
          W B.1.card ((B.1.filter fun i => S i).card) j else 0) = 1) →
    let X : Qubits n → Matrix (BoundedSupports n k) (BoundedSupports n k) ℝ :=
      fun S A B => (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
        W A.1.card ((A.1.filter fun i => S i).card) j *
        W B.1.card ((B.1.filter fun i => S i).card) j
    DualFeasible (fun A : BoundedSupports n k => A.1) X := by
  intro n k d W hmom
  dsimp only
  constructor
  · intro S
    change Matrix.PosSemidef (Matrix.of fun A B : BoundedSupports n k =>
      (2:ℝ)^(-n:ℤ) * ∑ j : Fin d,
        W A.1.card ((A.1.filter fun i => S i).card) j *
        W B.1.card ((B.1.filter fun i => S i).card) j)
    let v : Fin d → BoundedSupports n k → ℝ := fun j A =>
      W A.1.card ((A.1.filter fun i => S i).card) j
    have hj (j : Fin d) : Matrix.PosSemidef (Matrix.of fun A B => v j A * v j B) := by
      simpa [Matrix.vecMulVec] using Matrix.posSemidef_vecMulVec_self_star (v j)
    have hsum : Matrix.PosSemidef
        (∑ j : Fin d, (Matrix.of fun A B => v j A * v j B)) := by
      classical
      simpa using Matrix.posSemidef_sum (x := fun j : Fin d =>
        (Matrix.of fun A B => v j A * v j B)) Finset.univ (fun j _ => hj j)
    have hscale : (0 : ℝ) ≤ (2:ℝ)^(-n:ℤ) := by positivity
    have hscaled := hsum.smul hscale
    have heq :
        (Matrix.of fun A B : BoundedSupports n k =>
          (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, v j A * v j B) =
        (2:ℝ)^(-n:ℤ) • (∑ j : Fin d, (Matrix.of fun A B => v j A * v j B)) := by
      ext A B
      rw [Matrix.of_apply, Matrix.smul_apply]
      change (2:ℝ)^(-n:ℤ) * (∑ j : Fin d, v j A * v j B) =
        (2:ℝ)^(-n:ℤ) * ((∑ j : Fin d,
          (Matrix.of fun A B => v j A * v j B)) A B)
      congr 1
      simpa only [Matrix.of_apply] using
        (Matrix.sum_apply A B Finset.univ
          (fun j : Fin d => Matrix.of fun A B => v j A * v j B)).symm
    change Matrix.PosSemidef (Matrix.of fun A B : BoundedSupports n k =>
      (2:ℝ)^(-n:ℤ) * ∑ j : Fin d, v j A * v j B)
    rw [heq]
    exact hscaled
  · exact hmom
