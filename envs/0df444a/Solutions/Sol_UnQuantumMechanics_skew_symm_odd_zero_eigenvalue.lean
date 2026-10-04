-- Prove2me | solution 1 for UnQuantumMechanics.skew_symm_odd_zero_eigenvalue
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T01:30:50.779893+00:00
-- url     : https://prove2.me/submissions/481051fc-ac91-4d6c-a9ce-0f8e9bcac790

import Mathlib
import Definitions.Def_UnQM_phase_space

open Matrix

open Matrix in
theorem solution {ν : ℕ} (hν : Odd ν) (J : Matrix (Fin ν) (Fin ν) ℝ)
    (hJ : Jᵀ = -J) :
    Module.End.HasEigenvalue (Matrix.toLin' J) 0 := by
  have hdet : J.det = 0 := by
    have h1 : J.det = (-J).det := by rw [← hJ, Matrix.det_transpose]
    rw [Matrix.det_neg, Fintype.card_fin, hν.neg_one_pow] at h1
    linarith
  refine ((LinearMap.hasEigenvalue_zero_tfae (Matrix.toLin' J)).out 0 3).mpr ?_
  rw [LinearMap.det_toLin']
  exact hdet
