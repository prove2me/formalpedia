-- Prove2me | solution 1 for QCQPTightness.SOCP.dsdp_subset_dsocp
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T16:44:34.97483+00:00
-- url     : https://prove2.me/submissions/62c88dc1-65a6-47e5-9645-c3d5468d9f6a

import Definitions.Def_QCQPTightness_SOCP_Relaxation
import Theorems.Thm_QCQPTightness_SOCP_schur_diag_ge

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
    P.DSDP ⊆ P.DSOCP a₀ a := by
  intro p hp
  rcases hp with ⟨X, ⟨hXs, hY, hcons⟩, hobj⟩
  refine ⟨(fun j => X j j), ⟨?_, (QCQPTightness.SOCP.schur_diag_ge p.1 X hY).2⟩, ?_⟩
  · intro i
    constructor
    · intro hi
      have ht := (hcons i).1 hi
      rw [hdiag.2 i, trace_lift_diagonal] at ht
      exact ht
    · intro hi
      have ht := (hcons i).2 hi
      rw [hdiag.2 i, trace_lift_diagonal] at ht
      exact ht
  · rw [hdiag.1, trace_lift_diagonal] at hobj
    exact hobj

