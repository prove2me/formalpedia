-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.ideal_not_not_cp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T00:02:51.615017+00:00
-- url     : https://prove2.me/submissions/90255b77-8454-426c-b664-3e4f599908c2

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23
open QAlgorithms

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

theorem g74h_idealNot_apply (i j a b : Fin 2) :
    idealNot (Matrix.single i j 1) a b =
      (if i = j then (if a = b then 1 else 0) else 0) - (if a = i ∧ b = j then 1 else 0) := by
  fin_cases i <;> fin_cases j <;> fin_cases a <;> fin_cases b <;>
    simp [idealNot, Matrix.trace, Fin.sum_univ_two, Matrix.single_apply]

theorem solution :
    (∀ a b : Fin 2 × Fin 2, functionOutputChoi idealNot a b =
      (!![0,0,0,-1; 0,1,0,0; 0,0,1,0; -1,0,0,0] : Op (Fin 4))
        ⟨2*a.1.val+a.2.val, by omega⟩ ⟨2*b.1.val+b.2.val, by omega⟩) ∧
    ¬ CompletelyPositive idealNot ∧ ¬ IsChannel idealNot := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨a1, a2⟩ ⟨b1, b2⟩
    show idealNot (Matrix.single a2 b2 1) a1 b1 = _
    rw [g74h_idealNot_apply]
    fin_cases a1 <;> fin_cases a2 <;> fin_cases b1 <;> fin_cases b2 <;> simp [Matrix.vecHead, Matrix.vecTail]
  · intro h
    let v : Fin 2 × Fin 2 → ℂ := fun p => if p.1 = p.2 then 1 else 0
    have hX := h 2 (Matrix.vecMulVec v (star v)) (Matrix.posSemidef_vecMulVec_self_star v)
    have h2 := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hX).2 v
    have key : star v ⬝ᵥ ((idTensorSuperop idealNot (Matrix.vecMulVec v (star v)) :
        Op (Fin 2 × Fin 2)) *ᵥ v) = -2 := by
      have hm : ∀ p q : Fin 2 × Fin 2,
          (idTensorSuperop idealNot (Matrix.vecMulVec v (star v)) : Op (Fin 2 × Fin 2)) p q =
            idealNot (Matrix.single p.1 q.1 1) p.2 q.2 := by
        intro p q
        simp only [idTensorSuperop, Matrix.of_apply]
        congr 2
        ext i i'
        simp [v, Matrix.vecMulVec_apply, Matrix.single_apply]
        by_cases h1 : p.1 = i <;> by_cases h2 : q.1 = i' <;> simp [h1, h2, eq_comm]
      simp only [dotProduct, Matrix.mulVec, hm, g74h_idealNot_apply, Fintype.sum_prod_type,
        Fin.sum_univ_two, v]
      norm_num
    rw [key] at h2
    norm_num at h2
  · rintro ⟨m, E, -, hE⟩
    have hS : ∑ i : Fin 2, ∑ j : Fin 2, idealNot (Matrix.single i j 1) i j = -2 := by
      simp only [g74h_idealNot_apply, Fin.sum_univ_two]; norm_num
    have hS2 : ∑ i : Fin 2, ∑ j : Fin 2, idealNot (Matrix.single i j 1) i j =
        ∑ k, ((E k 0 0 + E k 1 1) * star (E k 0 0 + E k 1 1)) := by
      simp only [hE, krausApply, Matrix.sum_apply, Fin.sum_univ_two]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.single_apply, Matrix.conjTranspose_apply]
      ring
    have hnn : (0 : ℝ) ≤ (∑ k, ((E k 0 0 + E k 1 1) * star (E k 0 0 + E k 1 1))).re := by
      rw [Complex.re_sum]
      refine Finset.sum_nonneg fun k _ => ?_
      rw [Complex.star_def, Complex.mul_conj]
      simp [Complex.normSq_nonneg]
    rw [← hS2, hS] at hnn
    norm_num at hnn

end
