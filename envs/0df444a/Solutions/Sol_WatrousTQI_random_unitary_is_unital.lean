-- Prove2me | solution 1 for WatrousTQI.random_unitary_is_unital
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-12T18:11:49.70483+00:00
-- url     : https://prove2.me/submissions/fd3231f8-a3da-453b-96ee-f5929f86813e

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11
set_option autoImplicit false
noncomputable section
open scoped Matrix ComplexConjugate BigOperators




theorem solution {d : ℕ} (hd : 0 < d)
    (Φ : QAlgorithms.Superop (Fin d) (Fin d))
    (h : QAlgorithms.Papers.Independent.Dependency50.P11.IsRandomUnitary Φ) :
    Φ (1 : Matrix (Fin d) (Fin d) ℂ) = 1 := by
  classical
  obtain ⟨k, p, V, hp, hsum, hΦ⟩ := h
  rw [hΦ]
  have hU (j : Fin k) : (V j : Matrix (Fin d) (Fin d) ℂ) * 1 *
      (V j : Matrix (Fin d) (Fin d) ℂ)ᴴ = 1 := by
    simpa only [mul_one, Matrix.star_eq_conjTranspose] using (V j).property.2
  simp_rw [hU]
  rw [← Finset.sum_smul]
  have hs : (∑ j, (p j : ℂ)) = 1 := by rw [← Complex.ofReal_sum, hsum, Complex.ofReal_one]
  rw [hs, one_smul]
