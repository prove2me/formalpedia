-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P44.pairwiseSaturatedNotPositive
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T23:48:37.578116+00:00
-- url     : https://prove2.me/submissions/160416ec-99f0-4cb7-81ec-8ae991cfa00b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P44

namespace QAlgorithms.Papers.Independent.Information100.P44

noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

theorem g52c_rank_one_psd (M : Matrix (Fin 2) (Fin 2) ℂ) (s : ℂ) (hs : s = 1 ∨ s = -1)
    (hM : M = Matrix.vecMulVec ![1, s] (star ![1, s])) :
    M.PosSemidef ∧ M.rank = 1 := by
  refine ⟨hM ▸ Matrix.posSemidef_vecMulVec_self_star _, le_antisymm ?_ ?_⟩
  · rw [hM]; exact Matrix.rank_vecMulVec_le _ _
  · have h1 : M.submatrix (fun _ : Unit => (0 : Fin 2)) (fun _ : Unit => (0 : Fin 2)) = 1 := by
      ext i j; rw [Matrix.submatrix_apply, hM, Matrix.vecMulVec_apply]; simp
    have := Matrix.rank_submatrix_le M (fun _ : Unit => (0 : Fin 2)) (fun _ : Unit => (0 : Fin 2))
    rw [h1, Matrix.rank_one] at this
    simpa using this

end

end QAlgorithms.Papers.Independent.Information100.P44

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P44 in
open scoped ComplexConjugate ComplexOrder Matrix in
theorem solution :
    (∀ f : Fin 2 ↪ Fin 3,
      (frustration.submatrix f f).PosSemidef ∧ (frustration.submatrix f f).rank = 1) ∧
    ¬ frustration.PosSemidef := by
  constructor
  · intro f
    have hab : f 0 ≠ f 1 := fun h => by simpa using f.injective h
    have key : ∀ i j : Fin 3, i ≠ j → frustration i i = 1 ∧ frustration j j = 1 ∧
        frustration j i = frustration i j ∧ (frustration i j = 1 ∨ frustration i j = -1) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [frustration]
    obtain ⟨h1, h2, h3, h4⟩ := key _ _ hab
    refine g52c_rank_one_psd _ (frustration (f 0) (f 1)) h4 ?_
    have hst : star (frustration (f 0) (f 1)) = frustration (f 0) (f 1) := by
      rcases h4 with h | h <;> rw [h] <;> simp
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, h1, h2, h3, hst]
    rcases h4 with h | h <;> rw [h] <;> norm_num
  · intro h
    have := (Matrix.posSemidef_iff_dotProduct_mulVec.mp h).2 (![1, 1, -1] : Fin 3 → ℂ)
    simp [frustration, Matrix.mulVec, dotProduct, Fin.sum_univ_three] at this
    norm_num at this
