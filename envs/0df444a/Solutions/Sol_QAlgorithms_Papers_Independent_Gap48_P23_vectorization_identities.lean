-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P23.vectorization_identities
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T23:58:11.533348+00:00
-- url     : https://prove2.me/submissions/221a3b49-cc01-43c9-a3c3-146b9543166b

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P23
noncomputable section

open QAlgorithms.Papers.Independent.Gap48.P23

open MeasureTheory

open scoped ComplexConjugate Matrix ComplexOrder

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

-- Exact frozen coordinate helpers; no paper-local redeclarations.

open QAlgorithms.Papers.Independent.Information100.P58 (Word)

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

open QAlgorithms.Papers.Independent.Information100.P63 (tensorPower)

/-- PDF pp.45-46, Proposition A.2: all four identities, with the bilinear bra. -/
theorem solution (d : ℕ) (hd : 1 ≤ d) (A B : Op (Fin d)) :
    vectorizedBra B (bilinearVectorize A) = (A * B.transpose).trace ∧
    (vectorSwap d).mulVec (bilinearVectorize A) = bilinearVectorize A.transpose ∧
    (Matrix.kronecker B (1 : Op (Fin d))).mulVec (bilinearVectorize A) = bilinearVectorize (B*A) ∧
    singleContraction A B = A*B := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [vectorizedBra, bilinearVectorize, Matrix.trace, Matrix.diag, Matrix.mul_apply,
      Matrix.transpose_apply, Fintype.sum_prod_type]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => mul_comm _ _
  · funext x
    simp only [vectorSwap, Matrix.mulVec, dotProduct, bilinearVectorize, Matrix.transpose_apply,
      Fintype.sum_prod_type]
    rw [Finset.sum_eq_single x.2, Finset.sum_eq_single x.1]
    · simp
    · intro b _ hb; simp [Prod.ext_iff, Ne.symm hb]
    · simp
    · intro b _ hb
      apply Finset.sum_eq_zero; intro c _; simp [Prod.ext_iff, Ne.symm hb]
    · simp
  · funext x
    simp only [Matrix.mulVec, dotProduct, bilinearVectorize, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type, Matrix.mul_apply, Matrix.one_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single x.2]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  · funext a b
    simp [singleContraction, Matrix.mul_apply]


end
