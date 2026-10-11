-- Prove2me | solution 1 for QCQPTightness.SOCP.schur_diag_ge
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:10:08.676127+00:00
-- url     : https://prove2.me/submissions/7ed60137-5e60-44b6-aeb7-b943b3e80a01

import Definitions.Def_QCQPTightness_SOCP_QCQP

open Matrix
set_option autoImplicit false

theorem solution {N : ℕ} (x : Fin N → ℝ) (X : Matrix (Fin N) (Fin N) ℝ)
    (hY : (QCQPTightness.ConvHull.liftY x X).PosSemidef) :
    (X - Matrix.vecMulVec x x).PosSemidef ∧ ∀ j, x j ^ 2 ≤ X j j := by
  let B : Matrix (Fin 1) (Fin N) ℝ := fun _ j => x j
  haveI : Invertible (1 : Matrix (Fin 1) (Fin 1) ℝ) := invertibleOne
  have htop : (fun (_ _ : Fin 1) => (1 : ℝ)) =
      (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
    ext i j
    simp [Matrix.one_apply, Subsingleton.elim i j]
  have hblock : (Matrix.fromBlocks (1 : Matrix (Fin 1) (Fin 1) ℝ) B Bᴴ X).PosSemidef := by
    have hB : Bᴴ = (fun i (_ : Fin 1) => x i) := by
      ext i j
      rfl
    simpa [QCQPTightness.ConvHull.liftY, hB, B, htop] using hY
  have hC := (Matrix.PosDef.fromBlocks₁₁ B X
    (A := (1 : Matrix (Fin 1) (Fin 1) ℝ)) Matrix.PosDef.one).mp hblock
  have hprod : Bᴴ * B = Matrix.vecMulVec x x := by
    ext i j
    change (∑ _ : Fin 1, x i * x j) = x i * x j
    simp
  have hpsd : (X - Matrix.vecMulVec x x).PosSemidef := by
    simpa only [inv_one, Matrix.mul_one, hprod] using hC
  refine ⟨hpsd, fun j => ?_⟩
  have hj := hpsd.diag_nonneg (i := j)
  simp only [Matrix.sub_apply, Matrix.vecMulVec_apply] at hj
  nlinarith

