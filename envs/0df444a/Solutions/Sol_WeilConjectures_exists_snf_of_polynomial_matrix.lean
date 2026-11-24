-- Prove2me | solution 1 for WeilConjectures.exists_snf_of_polynomial_matrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:51:31.211021+00:00
-- url     : https://prove2.me/submissions/82473524-f988-456e-a8c4-0856f092c3b8
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_diagonal_of_pid_matrix

/-!
Phase 1: SNF diagonal + classification from PID-lift child.
Phase 2: assemble `rcf` / `sim` by choosing representatives per factor list (A39).
-/

open Matrix Classical

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (invFactors : Matrix ι ι (Polynomial K) → List (Polynomial K))
      (rcf : List (Polynomial K) → Matrix ι ι K)
      (sim : Matrix ι ι K → ((ι → K) ≃ₗ[K] (ι → K))),
      (∀ M, invFactors M = invFactors M.transpose) ∧
      (∀ A, (sim A).conj (Matrix.toLin' A) =
        Matrix.toLin' (rcf (invFactors (Matrix.charmatrix A)))) := by
  obtain ⟨diag, htr, hclass⟩ :=
    WeilConjectures.exists_snf_diagonal_of_pid_matrix (K := K) (ι := ι)
  -- Phase 2: representative matrix for each factor list (default `0` if unrealized)
  let rcf : List (Polynomial K) → Matrix ι ι K := fun fs =>
    if h : ∃ A : Matrix ι ι K, diag (charmatrix A) = fs then
      Classical.choose h
    else
      0
  have hrcf (A : Matrix ι ι K) :
      diag (charmatrix (rcf (diag (charmatrix A)))) = diag (charmatrix A) := by
    dsimp [rcf]
    have hEx : ∃ B : Matrix ι ι K, diag (charmatrix B) = diag (charmatrix A) := ⟨A, rfl⟩
    rw [dif_pos hEx]
    exact Classical.choose_spec hEx
  -- Similarity A ∼ rcf (diag (charmatrix A)) via classification
  let sim : Matrix ι ι K → ((ι → K) ≃ₗ[K] (ι → K)) := fun A =>
    Classical.choose (hclass A (rcf (diag (charmatrix A))) (hrcf A).symm)
  have hsim (A : Matrix ι ι K) :
      (sim A).conj (Matrix.toLin' A) =
        Matrix.toLin' (rcf (diag (charmatrix A))) :=
    Classical.choose_spec (hclass A (rcf (diag (charmatrix A))) (hrcf A).symm)
  refine ⟨diag, rcf, sim, htr, ?_⟩
  intro A
  simpa using hsim A
