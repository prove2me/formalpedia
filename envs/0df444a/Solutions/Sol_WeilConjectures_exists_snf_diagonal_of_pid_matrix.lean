-- Prove2me | solution 1 for WeilConjectures.exists_snf_diagonal_of_pid_matrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T02:03:40.547506+00:00
-- url     : https://prove2.me/submissions/f5f5fcaa-462c-4639-a10a-0e517c3411eb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_snf_diag_factorization_of_poly_matrix
import Theorems.Thm_WeilConjectures_similar_of_snf_diag_eq_on_charmatrix

/-!
A40: obtain PID-lift `d` with transpose + factorization.
A41: classify via `similar_of_snf_diag_eq_on_charmatrix` on the same `d`.
`diag` reads `d` along `Fintype.equivFin` via `List.ofFn` (injective).
-/

open Matrix

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι] :
    ∃ (diag : Matrix ι ι (Polynomial K) → List (Polynomial K)),
      (∀ M, diag M = diag M.transpose) ∧
      (∀ A B : Matrix ι ι K,
        diag (Matrix.charmatrix A) = diag (Matrix.charmatrix B) →
        ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
          P.conj (Matrix.toLin' A) = Matrix.toLin' B) := by
  obtain ⟨d, htr, hfac⟩ :=
    WeilConjectures.exists_snf_diag_factorization_of_poly_matrix (K := K) (ι := ι)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let diag : Matrix ι ι (Polynomial K) → List (Polynomial K) := fun M =>
    List.ofFn fun j : Fin (Fintype.card ι) => d M (e.symm j)
  refine ⟨diag, ?_, ?_⟩
  · intro M
    dsimp [diag]
    refine congrArg List.ofFn ?_
    funext j
    exact htr M (e.symm j)
  · intro A B hList
    have hFin :
        (fun j : Fin (Fintype.card ι) => d (charmatrix A) (e.symm j)) =
          (fun j => d (charmatrix B) (e.symm j)) :=
      List.ofFn_inj.mp hList
    have hFun : d (charmatrix A) = d (charmatrix B) := by
      funext i
      simpa using congrFun hFin (e i)
    exact WeilConjectures.similar_of_snf_diag_eq_on_charmatrix d hfac hFun
