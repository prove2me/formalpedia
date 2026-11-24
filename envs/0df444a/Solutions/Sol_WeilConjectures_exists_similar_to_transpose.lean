-- Prove2me | solution 1 for WeilConjectures.exists_similar_to_transpose
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T01:12:35.813264+00:00
-- url     : https://prove2.me/submissions/858aaec3-069a-4366-9b7d-e99f1dc1550f

import Mathlib
import Theorems.Thm_WeilConjectures_exists_similar_to_companion

/-!
From a common rational-canonical form `C` for `A` and `Aᵀ`, compose similarities:
`A --P--> C <--Q-- Aᵀ` yields `A --P.trans Q.symm--> Aᵀ`.
-/

open Matrix

theorem solution
    {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι K) :
    ∃ (P : (ι → K) ≃ₗ[K] (ι → K)),
      P.conj (Matrix.toLin' A) = Matrix.toLin' A.transpose := by
  obtain ⟨C, P, Q, hP, hQ⟩ := WeilConjectures.exists_similar_to_companion A
  refine ⟨P.trans Q.symm, ?_⟩
  have hcomp :
      (P.trans Q.symm).conj (Matrix.toLin' A) =
        Q.symm.conj (P.conj (Matrix.toLin' A)) := by
    ext x
    simp [LinearEquiv.conj_apply, LinearEquiv.trans_apply]
  have hQ' : Q.symm.conj (Matrix.toLin' C) = Matrix.toLin' A.transpose := by
    -- from `Q.conj (toLin' Aᵀ) = toLin' C` via `conj_symm_conj`
    calc Q.symm.conj (Matrix.toLin' C)
        = Q.symm.conj (Q.conj (Matrix.toLin' A.transpose)) := by rw [← hQ]
      _ = Matrix.toLin' A.transpose := by simp [LinearEquiv.conj_symm_conj]
  calc (P.trans Q.symm).conj (Matrix.toLin' A)
      = Q.symm.conj (P.conj (Matrix.toLin' A)) := hcomp
    _ = Q.symm.conj (Matrix.toLin' C) := by rw [hP]
    _ = Matrix.toLin' A.transpose := hQ'
