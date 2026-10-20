-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Frontier18.P17.transpose_positive_notCP
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:37:59.322602+00:00
-- url     : https://prove2.me/submissions/bea8e819-7628-4abe-b5b9-fd2034f05dbf

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Frontier18_P17

noncomputable section
open scoped BigOperators Matrix ComplexConjugate ComplexOrder TensorProduct

open QAlgorithms.Papers.Independent.Dependency50.P49 (transposeMap)

theorem solution :
    (∀ N : ℕ, 0 < N → ∀ X : Matrix (Fin N) (Fin N) ℂ,
      X.PosSemidef → (transposeMap N X).PosSemidef) ∧
    ¬ QAlgorithms.Entanglement.IsCompletelyPositive (transposeMap 2) := by
  refine ⟨fun N _ X hX => hX.transpose, fun h => ?_⟩
  let Ω : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
  have hX := Matrix.posSemidef_vecMulVec_self_star Ω
  have hY := h 2 _ hX
  rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hY
  let w : Fin 2 × Fin 2 → ℂ := fun p => if p = (0, 1) then 1 else if p = (1, 0) then -1 else 0
  have h2 := hY.2 w
  have : star w ⬝ᵥ (QAlgorithms.idTensorSuperop (transposeMap 2)
      (Matrix.vecMulVec Ω (star Ω)) *ᵥ w) = -2 := by
    simp [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two, w, Ω,
      QAlgorithms.idTensorSuperop, transposeMap, Matrix.vecMulVec]
    norm_num
  rw [this] at h2
  norm_num at h2
