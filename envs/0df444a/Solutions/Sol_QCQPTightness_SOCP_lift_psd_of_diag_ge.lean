-- Prove2me | solution 1 for QCQPTightness.SOCP.lift_psd_of_diag_ge
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:17:45.37298+00:00
-- url     : https://prove2.me/submissions/04539276-d842-4a9a-947e-288916dc3998

import Definitions.Def_QCQPTightness_SOCP_QCQP

open Matrix
set_option autoImplicit false

theorem solution {N : ℕ} (x y : Fin N → ℝ) (hxy : ∀ j, x j ^ 2 ≤ y j) :
    (QCQPTightness.ConvHull.liftY x
      (Matrix.of fun j k => if j = k then y j else x j * x k)).PosSemidef := by
  let X : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun j k => if j = k then y j else x j * x k
  have hdiff : X - Matrix.vecMulVec x x = Matrix.diagonal (fun j => y j - x j ^ 2) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [X, Matrix.of_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
        Matrix.diagonal_apply, pow_two]
    · simp [X, Matrix.of_apply, Matrix.sub_apply, Matrix.vecMulVec_apply,
        Matrix.diagonal_apply, hij]
  have hpsd : (X - Matrix.vecMulVec x x).PosSemidef := by
    rw [hdiff]
    exact Matrix.PosSemidef.diagonal (fun j => sub_nonneg.mpr (hxy j))
  let B : Matrix (Fin 1) (Fin N) ℝ := fun _ j => x j
  haveI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  have hprod : Bᴴ * B = Matrix.vecMulVec x x := by
    ext i j
    change (∑ _ : Fin 1, x i * x j) = x i * x j
    simp
  have hblock : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) B Bᴴ X).PosSemidef := by
    apply (Matrix.PosDef.fromBlocks₁₁ B X Matrix.PosDef.one).mpr
    simpa only [inv_one, Matrix.mul_one, hprod] using hpsd
  have htop : (fun (_ _ : Fin 1) => (1 : ℝ)) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [Matrix.one_apply, Subsingleton.elim i j]
  have hB : Bᴴ = (fun i (_ : Fin 1) => x i) := by
    ext i j
    rfl
  simpa [QCQPTightness.ConvHull.liftY, hB, B, htop, X] using hblock

