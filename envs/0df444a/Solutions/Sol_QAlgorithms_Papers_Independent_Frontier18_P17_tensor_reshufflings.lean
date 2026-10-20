-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.tensor_reshufflings
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:41:06.727598+00:00
-- url     : https://prove2.me/submissions/263e807e-eadc-465f-a689-45f6dbefb9e0

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct
open QAlgorithms.Papers.Independent.Frontier18.P17
open QAlgorithms.Papers.Independent.Information100.P30 (tensorMap depolarizing)
open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)


theorem solution {n m : ℕ}
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin m) (Fin m) ℂ) :
    res (reshuffle (Matrix.kronecker A B)) = QAlgorithms.tensorVec (res A) (res B) ∧
    vec (alternateReshuffle (Matrix.kronecker A B)) = QAlgorithms.tensorVec (vec A) (vec B) := by
  constructor <;> rfl
