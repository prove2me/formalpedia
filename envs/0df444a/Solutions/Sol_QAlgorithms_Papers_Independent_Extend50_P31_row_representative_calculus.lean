-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P31.row_representative_calculus
-- status  : ACCEPTED   (prove)
-- author  : @Mrnaiq
-- created : 2026-11-14T05:03:10.009384+00:00
-- url     : https://prove2.me/submissions/0eeac5aa-d61e-49e4-8c06-956c0d5edd59

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P31
noncomputable section
open QAlgorithms.Papers.Independent.Extend50.P31 QAlgorithms.Papers.Independent.Information100.P44 QAlgorithms.Papers.Independent.Dependency50.P16
open scoped Matrix ComplexConjugate
set_option autoImplicit false

set_option autoImplicit false

set_option autoImplicit false

theorem solution (n : ℕ) :
    (∀ (Phi : EndMat n) (X : Mat n), rowVec (Phi X) =
      (rowMatrixRepresentative Phi).mulVec (rowVec X)) ∧
    (∀ Phi Psi : EndMat n, rowMatrixRepresentative (Phi.comp Psi) =
      rowMatrixRepresentative Phi * rowMatrixRepresentative Psi) ∧
    (∀ A B : Mat n, rowMatrixRepresentative (sandwich A B) = Matrix.kronecker A Bᵀ) := by
  classical
  have ha (Phi : EndMat n) (X : Mat n) : rowVec (Phi X) =
      (rowMatrixRepresentative Phi).mulVec (rowVec X) := by
    have hx : X = ∑ a, ∑ b, X a b • matrixUnit a b := by
      ext i j
      simp only [Matrix.sum_apply]
      change X i j = ∑ a, ∑ b, X a b * matrixUnit a b i j
      simp [matrixUnit, Matrix.single_apply, ite_and]
    have hf := congrArg Phi hx
    simp only [map_sum, map_smul] at hf
    ext ⟨i,j⟩
    rw [hf]
    change (∑ a, ∑ b, X a b • Phi (matrixUnit a b)) i j =
      ∑ p : Fin n × Fin n, Phi (matrixUnit p.1 p.2) i j * X p.1 p.2
    simp only [Matrix.sum_apply, Fintype.sum_prod_type]
    change (∑ a, ∑ b, X a b * Phi (matrixUnit a b) i j) = _
    simp only [mul_comm]
  refine ⟨ha, ?_, ?_⟩
  · intro Phi Psi
    ext ⟨i,j⟩ ⟨a,b⟩
    have hh := congrFun (ha Phi (Psi (matrixUnit a b))) (i,j)
    exact hh
  · intro A B
    ext ⟨i,j⟩ ⟨a,b⟩
    change (A * (matrixUnit a b * B)) i j = A i a * B b j
    simp [Matrix.mul_apply, matrixUnit, Matrix.single_apply, ite_and]