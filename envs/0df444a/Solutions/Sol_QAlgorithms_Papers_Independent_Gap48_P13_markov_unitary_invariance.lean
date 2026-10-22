-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P13.markov_unitary_invariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T22:55:32.704364+00:00
-- url     : https://prove2.me/submissions/0b9e77aa-49f6-4773-aba5-91a7c1afcae8

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P13
noncomputable section

open Filter MeasureTheory

open scoped BigOperators Topology ENNReal ComplexOrder Matrix Matrix.Norms.L2Operator

attribute [local instance] Classical.propDecidable Classical.decEq

attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

open QAlgorithms.Papers.Independent.Gap48.P13

open QAlgorithms.Papers.Independent.Information100.P63 (Mat)

open QAlgorithms.Papers.Independent.Dependency50.P21 (imaginaryPower)

theorem g73w_cfc_conj {L : Type*} [Fintype L] [DecidableEq L] (V : Matrix.unitaryGroup L ℂ)
    (B : Mat L) (hB : B.IsHermitian) (f : ℝ → ℝ) :
    cfc f ((V : Mat L).conjTranspose * B * (V : Mat L)) =
      (V : Mat L).conjTranspose * cfc f B * (V : Mat L) := by
  have hc : Continuous (Unitary.conjStarAlgAut ℂ (Mat L) (star V)) :=
    LinearMap.continuous_of_finiteDimensional
      ((Unitary.conjStarAlgAut ℂ (Mat L) (star V)).toAlgEquiv.toLinearEquiv.toLinearMap)
  have hsa : IsSelfAdjoint B := hB
  have hsa2 : IsSelfAdjoint (Unitary.conjStarAlgAut ℂ (Mat L) (star V) B) := by
    rw [Unitary.conjStarAlgAut_star_apply]
    exact hsa.conjugate' _
  have := StarAlgHomClass.map_cfc (S := ℂ) (Unitary.conjStarAlgAut ℂ (Mat L) (star V)) f B
    ((Matrix.finite_real_spectrum (A := B)).continuousOn _) hc hsa hsa2
  rw [Unitary.conjStarAlgAut_star_apply, Unitary.conjStarAlgAut_star_apply] at this
  simpa [Matrix.star_eq_conjTranspose] using this.symm

theorem g73w_ent_conj {L : Type*} [Fintype L] [DecidableEq L] (V : Matrix.unitaryGroup L ℂ)
    (B : Mat L) (hB : B.IsHermitian) :
    covarianceEntropy ((V : Mat L).conjTranspose * B * (V : Mat L)) = covarianceEntropy B := by
  unfold covarianceEntropy
  rw [g73w_cfc_conj V B hB, Matrix.trace_mul_cycle]
  have : (V : Mat L) * (V : Mat L).conjTranspose = 1 := by
    have := Unitary.mul_star_self_of_mem V.2
    simpa [Matrix.star_eq_conjTranspose] using this
  rw [this, one_mul]

theorem g73w_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (M : Mat (α ⊕ β)) (V1 : Mat α) (V2 : Mat β) :
    ((Matrix.fromBlocks V1 0 0 V2).conjTranspose * M * Matrix.fromBlocks V1 0 0 V2).toBlocks₁₁ =
      V1.conjTranspose * M.toBlocks₁₁ * V1 ∧
    ((Matrix.fromBlocks V1 0 0 V2).conjTranspose * M * Matrix.fromBlocks V1 0 0 V2).toBlocks₂₂ =
      V2.conjTranspose * M.toBlocks₂₂ * V2 := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks M]
  conv_rhs => skip
  rw [← Matrix.fromBlocks_toBlocks M]
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

theorem g73w_unit_blocks {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (V1 : Matrix.unitaryGroup α ℂ) (V2 : Matrix.unitaryGroup β ℂ) :
    Matrix.fromBlocks (V1 : Mat α) 0 0 (V2 : Mat β) ∈ Matrix.unitaryGroup (α ⊕ β) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  have h1 := Unitary.star_mul_self_of_mem V1.2
  have h2 := Unitary.star_mul_self_of_mem V2.2
  rw [Matrix.star_eq_conjTranspose] at h1 h2 ⊢
  simp [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, h1, h2,
    Matrix.fromBlocks_one]
variable {I J K : Type*} [Fintype I] [Fintype J] [Fintype K]
  [DecidableEq I] [DecidableEq J] [DecidableEq K]

theorem solution (A : Mat (I ⊕ (J ⊕ K))) (hA : A.PosSemidef)
    (U1 : Matrix.unitaryGroup I ℂ) (U2 : Matrix.unitaryGroup J ℂ)
    (U3 : Matrix.unitaryGroup K ℂ) (hMarkov : IsMarkov A) :
    let U := diagonal3 (U1 : Mat I) (U2 : Mat J) (U3 : Mat K)
    IsMarkov (U.conjTranspose * A * U) := by
  intro U
  have hH : A.IsHermitian := hA.1
  let V23 : Matrix.unitaryGroup (J ⊕ K) ℂ := ⟨_, g73w_unit_blocks U2 U3⟩
  let W12 : Matrix.unitaryGroup (I ⊕ J) ℂ := ⟨_, g73w_unit_blocks U1 U2⟩
  let Uu : Matrix.unitaryGroup (I ⊕ (J ⊕ K)) ℂ := ⟨_, g73w_unit_blocks U1 V23⟩
  have hU : U = (Uu : Mat (I ⊕ (J ⊕ K))) := rfl
  -- marginal23
  have h23 : marginal23 (U.conjTranspose * A * U) =
      (V23 : Mat (J ⊕ K)).conjTranspose * marginal23 A * (V23 : Mat (J ⊕ K)) :=
    (g73w_blocks A (U1 : Mat I) (V23 : Mat (J ⊕ K))).2
  have h22 : a22 (U.conjTranspose * A * U) =
      (U2 : Mat J).conjTranspose * a22 A * (U2 : Mat J) := by
    have : a22 (U.conjTranspose * A * U) = (marginal23 (U.conjTranspose * A * U)).toBlocks₁₁ := rfl
    rw [this, h23]
    exact (g73w_blocks (marginal23 A) (U2 : Mat J) (U3 : Mat K)).1
  have h12 : marginal12 (U.conjTranspose * A * U) =
      (W12 : Mat (I ⊕ J)).conjTranspose * marginal12 A * (W12 : Mat (I ⊕ J)) := by
    let e := Equiv.sumAssoc I J K
    have hm : ∀ M : Mat (I ⊕ (J ⊕ K)), marginal12 M = (M.submatrix e e).toBlocks₁₁ := by
      intro M; ext a b; rcases a with a | a <;> rcases b with b | b <;> rfl
    have hUe : U.submatrix e e = Matrix.fromBlocks (W12 : Mat (I ⊕ J)) 0 0 (U3 : Mat K) := by
      ext a b
      rcases a with (a | a) | a <;> rcases b with (b | b) | b <;> rfl
    rw [hm, hm, ← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e,
      ← Matrix.conjTranspose_submatrix, hUe]
    exact (g73w_blocks (A.submatrix e e) (W12 : Mat (I ⊕ J)) (U3 : Mat K)).1
  unfold IsMarkov at hMarkov ⊢
  rw [h23, h22, h12, hU, g73w_ent_conj, g73w_ent_conj, g73w_ent_conj, g73w_ent_conj]
  · exact hMarkov
  · exact hH.submatrix _
  · exact hH.submatrix _
  · exact hH.submatrix _
  · exact hH
