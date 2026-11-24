-- Prove2me | solution 1 for WeilConjectures.similar_of_snf_diag_eq_on_charmatrix
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T05:24:25.938095+00:00
-- url     : https://prove2.me/submissions/7282b1b1-f546-486a-aa8e-e8fe6ef10b06
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeilConjectures_exists_unit_equiv_of_snf_diag_eq
import Theorems.Thm_WeilConjectures_similar_of_charmatrix_unit_equiv

/-!
A41 dual: equal SNF diag ⇒ unit equiv of charmatrices; then similarity.
-/

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (d : Matrix ι ι (Polynomial K) → (ι → Polynomial K))
    (hfac : ∀ M, ∃ (P Q : Matrix ι ι (Polynomial K)),
      IsUnit P.det ∧ IsUnit Q.det ∧
        P * M * Q = Matrix.diagonal (d M))
    {A B : Matrix ι ι K}
    (h : d (Matrix.charmatrix A) = d (Matrix.charmatrix B)) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' B := by
  refine WeilConjectures.similar_of_charmatrix_unit_equiv ?_
  exact WeilConjectures.exists_unit_equiv_of_snf_diag_eq d hfac h
