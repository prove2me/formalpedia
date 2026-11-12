-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.lemma6_character
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-12T01:55:39.909428+00:00
-- url     : https://prove2.me/submissions/463ce530-5414-4bd2-86c4-0706a5ed3032

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder

attribute [local instance] Classical.propDecidable Classical.decEq

open QAlgorithms.Papers.Independent.Information100.P44 (Mat matrixUnit)

open QAlgorithms.Papers.Independent.Dependency50.P16 (sandwich)

variable {G A : Type*} [Group G] [Fintype G] [Fintype A] [DecidableEq A] {n : ℕ}

open QAlgorithms.Papers.Independent.Extend50.P31 in
theorem solution (hG : Finite G) (U : UnitaryIrrep G n) (g : G) :
    rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g ∧
    Matrix.trace (rowMatrixRepresentative (conjugationMap U g)) = Matrix.trace (tensorConjugate U g) ∧
    Matrix.trace (rowMatrixRepresentative (conjugationMap U g)) = (Complex.normSq (character U g) : ℂ) := by
  have hentry : ∀ i j a b : Fin n,
      conjugationMap U g (matrixUnit a b) i j = U.rho g i a * conj (U.rho g j b) := by
    intro i j a b
    simp only [conjugationMap, sandwich, LinearMap.comp_apply, LinearMap.mulLeft_apply,
      LinearMap.mulRight_apply]
    rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [matrixUnit, Matrix.single_mul_apply_same, one_mul, Matrix.conjTranspose_apply]
      rfl
    · intro k _ hk
      rw [matrixUnit, Matrix.single_mul_apply_of_ne _ _ _ _ _ hk, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have p1 : rowMatrixRepresentative (conjugationMap U g) = tensorConjugate U g := by
    ext ⟨i, j⟩ ⟨a, b⟩
    show conjugationMap U g (matrixUnit a b) i j = _
    rw [hentry]
    rfl
  refine ⟨p1, by rw [p1], ?_⟩
  rw [p1]
  have ht : Matrix.trace (tensorConjugate U g) =
      Matrix.trace (U.rho g) * conj (Matrix.trace (U.rho g)) := by
    unfold tensorConjugate
    simp only [Matrix.trace, Matrix.diag, Matrix.kronecker, Matrix.kroneckerMap_apply,
      Fintype.sum_prod_type]
    rw [map_sum, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => rfl))
  unfold character
  rw [ht, Complex.mul_conj]

end
