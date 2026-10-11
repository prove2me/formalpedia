-- Prove2me | solution 1 for QCQPTightness.SOCP.dsocp_subset_dsdp
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T17:53:57.658983+00:00
-- url     : https://prove2.me/submissions/1f0b1f65-a657-4c39-a1b2-0088c6cdad25

import Definitions.Def_QCQPTightness_SOCP_Relaxation
import Theorems.Thm_QCQPTightness_SOCP_lift_psd_of_diag_ge

open Matrix QCQPTightness.SOCP
set_option autoImplicit false

private lemma trace_lift_diagonal {N : ℕ} (a b x : Fin N → ℝ) (c : ℝ)
    (X : Matrix (Fin N) (Fin N) ℝ) :
    (QCQPTightness.ConvHull.liftQ (Matrix.diagonal a) b c *
      QCQPTightness.ConvHull.liftY x X).trace =
      a ⬝ᵥ (fun j => X j j) + 2 * (b ⬝ᵥ x) + c := by
  simp [QCQPTightness.ConvHull.liftQ, QCQPTightness.ConvHull.liftY,
    Matrix.fromBlocks, Matrix.of_apply, Matrix.trace, Matrix.diag, Fintype.sum_sum_type,
    Fin.sum_univ_one, Matrix.mul_apply, Matrix.diagonal, Finset.sum_add_distrib,
    dotProduct, ite_mul]
  ring

theorem solution {N m : ℕ} (P : QCQP N m) (a₀ : Fin N → ℝ) (a : Fin m → Fin N → ℝ)
    (hdiag : P.IsDiagonalQCQP a₀ a) :
    P.DSOCP a₀ a ⊆ P.DSDP := by
  intro p hp
  rcases hp with ⟨y, ⟨hcons, hxy⟩, hobj⟩
  let X : Matrix (Fin N) (Fin N) ℝ :=
    Matrix.of fun j k => if j = k then y j else p.1 j * p.1 k
  have hX : X.IsSymm := by
    change Xᵀ = X
    ext i j
    dsimp [X]
    by_cases hij : i = j
    · subst j; rfl
    · simp [hij, Ne.symm hij, mul_comm]
  have hdiagX : (fun j => X j j) = y := by
    funext j; simp [X]
  refine ⟨X, ⟨hX, QCQPTightness.SOCP.lift_psd_of_diag_ge p.1 y hxy, ?_⟩, ?_⟩
  · intro i
    constructor
    · intro hi
      rw [hdiag.2 i, trace_lift_diagonal, hdiagX]
      exact (hcons i).1 hi
    · intro hi
      rw [hdiag.2 i, trace_lift_diagonal, hdiagX]
      exact (hcons i).2 hi
  · rw [hdiag.1, trace_lift_diagonal, hdiagX]
    exact hobj
