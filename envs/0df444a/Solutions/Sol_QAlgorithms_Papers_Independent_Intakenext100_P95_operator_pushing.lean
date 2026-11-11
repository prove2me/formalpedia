-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakenext100.P95.operator_pushing
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T06:12:31.733023+00:00
-- url     : https://prove2.me/submissions/e231fa50-9f24-46f5-82bd-37127fa1c6c9

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.Linarith

open scoped Matrix ComplexConjugate
open scoped Matrix.Norms.L2Operator

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem solution {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (T : Matrix B A ℂ) (hT : Tᴴ * T = 1)
    (O : Matrix A A ℂ) :
    T * O = (T * O * Tᴴ) * T ∧
    ‖Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ) (T * O * Tᴴ)‖ =
      ‖Matrix.toEuclideanCLM (n := A) (𝕜 := ℂ) O‖ := by
  have hnorm : ‖T‖ ≤ 1 := by
    have h := Matrix.l2_opNorm_conjTranspose_mul_self T
    rw [hT] at h
    have hone : ‖(1 : Matrix A A ℂ)‖ ≤ 1 := by
      rw [← Matrix.l2_opNorm_toEuclideanCLM, map_one]
      exact ContinuousLinearMap.norm_id_le
    nlinarith [norm_nonneg T]
  have hnormStar : ‖Tᴴ‖ ≤ 1 := by
    simpa only [Matrix.l2_opNorm_conjTranspose] using hnorm
  constructor
  · simp only [Matrix.mul_assoc, hT, Matrix.mul_one]
  · simp only [Matrix.l2_opNorm_toEuclideanCLM]
    apply le_antisymm
    · calc
        ‖T * O * Tᴴ‖ ≤ ‖T * O‖ * ‖Tᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖T * O‖ := mul_le_of_le_one_right (norm_nonneg _) hnormStar
        _ ≤ ‖T‖ * ‖O‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖O‖ := mul_le_of_le_one_left (norm_nonneg _) hnorm
    · have hrecover : Tᴴ * (T * O * Tᴴ) * T = O := by
        calc
          Tᴴ * (T * O * Tᴴ) * T = (Tᴴ * T) * O * (Tᴴ * T) := by
            simp only [Matrix.mul_assoc]
          _ = O := by rw [hT, Matrix.one_mul, Matrix.mul_one]
      calc
        ‖O‖ = ‖Tᴴ * (T * O * Tᴴ) * T‖ := congrArg norm hrecover.symm
        _ ≤ ‖Tᴴ * (T * O * Tᴴ)‖ * ‖T‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖Tᴴ * (T * O * Tᴴ)‖ := mul_le_of_le_one_right (norm_nonneg _) hnorm
        _ ≤ ‖Tᴴ‖ * ‖T * O * Tᴴ‖ := Matrix.l2_opNorm_mul _ _
        _ ≤ ‖T * O * Tᴴ‖ := mul_le_of_le_one_left (norm_nonneg _) hnormStar

end


#print axioms solution
