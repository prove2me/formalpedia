-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Independent1.P02.cq_qc_image_dimension
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T11:36:37.612083+00:00
-- url     : https://prove2.me/submissions/eb381256-cc31-4968-bea3-080f65ffaf6f

import Definitions.Def_QAlgorithms_Defs_HolevoMatrixMaps
import Definitions.Def_QAlgorithms_Defs_FiniteRegisters
import Definitions.Def_QAlgorithms_Papers_Independent_Independent1_P02_Model
set_option autoImplicit false

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Independent1 QAlgorithms.Papers.Independent.Independent1.P02
open scoped Matrix ComplexOrder ComplexConjugate
attribute [local instance] Classical.propDecidable
attribute [local instance] Classical.decEq

lemma S170bM_im {d : ℕ} (A B : Algebra d) (hA : A.IsHermitian) (hB : B.IsHermitian) :
    ((A * B).trace).im = 0 := by
  have h : star ((A * B).trace) = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq, Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

lemma S170bM_complete {d : ℕ} (e : OrthonormalBasis (Fin d) ℂ (StateVector d)) :
    ∑ k, pureDensity (e k) = 1 := by
  ext a b
  simp only [Matrix.sum_apply, pureDensity, Matrix.of_apply, Matrix.one_apply]
  have := e.sum_inner_mul_inner (EuclideanSpace.single a (1 : ℂ)) (EuclideanSpace.single b (1 : ℂ))
  simp only [EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, map_one, one_mul,
    mul_one] at this
  rw [this]
  by_cases h : a = b
  · subst h; simp
  · simp [h, Ne.symm h]

lemma S170bM_key {d : ℕ} (hd : 0 < d) (G : HermitianFrame d) (R F : Fin d → Algebra d)
    (hR : ∀ m, (R m).IsHermitian) (hF : ∀ m, (F m).IsHermitian) (hsum : ∑ m, F m = 1) :
    (coordinateMatrix G (Entanglement.holevoMap R F)).rank ≤ d ∧
    Module.finrank ℝ (affineSpan ℝ ((Entanglement.holevoMap R F) ''
      {rho : Algebra d | IsDensityMatrix rho})).direction ≤ d-1 := by
  constructor
  · let W : Matrix (Fin (d ^ 2)) (Fin d) ℝ := Matrix.of fun j m => (G.matrix j * R m).trace.re
    let U : Matrix (Fin d) (Fin (d ^ 2)) ℝ := Matrix.of fun m k => (F m * G.matrix k).trace.re
    have hWU : coordinateMatrix G (Entanglement.holevoMap R F) = W * U := by
      ext j k
      simp only [coordinateMatrix, Matrix.of_apply, Matrix.mul_apply, W, U, Entanglement.holevoMap,
        LinearMap.coe_mk, AddHom.coe_mk, Matrix.mul_sum, Matrix.trace_sum, Matrix.mul_smul,
        Matrix.trace_smul, smul_eq_mul, Complex.re_sum]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [Complex.mul_re, S170bM_im _ _ (hF m) (G.hermitian k), zero_mul, sub_zero, mul_comm]
    rw [hWU]
    exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_le_width W).trans (by simp))
  · have hmem : ∀ rho ∈ {rho : Algebra d | IsDensityMatrix rho},
        Entanglement.holevoMap R F rho ∈ affineSpan ℝ (Set.range R) := by
      intro rho hrho
      have hrh : rho.IsHermitian := hrho.1.isHermitian
      let w : Fin d → ℝ := fun m => ((F m * rho).trace).re
      have hw : ∑ m ∈ Finset.univ, w m = 1 := by
        have : ∑ m, (F m * rho).trace = 1 := by
          rw [← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul, hrho.2]
        have h2 := congrArg Complex.re this
        simpa [w, Complex.re_sum] using h2
      have heq : Entanglement.holevoMap R F rho = Finset.univ.affineCombination ℝ R w := by
        rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
        simp only [Entanglement.holevoMap, LinearMap.coe_mk, AddHom.coe_mk]
        refine Finset.sum_congr rfl fun m _ => ?_
        have hc : (F m * rho).trace = ((w m : ℝ) : ℂ) := by
          apply Complex.ext
          · simp [w]
          · simp [S170bM_im _ _ (hF m) hrh]
        rw [hc, ← Complex.coe_smul]
      rw [heq]
      exact affineCombination_mem_affineSpan hw R
    have hle : (affineSpan ℝ ((Entanglement.holevoMap R F) '' {rho : Algebra d | IsDensityMatrix rho})).direction ≤
        vectorSpan ℝ (Set.range R) := by
      rw [← direction_affineSpan]
      apply AffineSubspace.direction_le
      apply affineSpan_le.2
      rintro _ ⟨rho, hrho, rfl⟩
      exact hmem rho hrho
    exact (Submodule.finrank_mono hle).trans (finrank_vectorSpan_range_le ℝ R (by simp; omega))


theorem solution (d : ℕ) (G : HermitianFrame d) (Phi : Endomorphism d)
    (hClass : IsCQ Phi ∨ IsQC Phi) :
    (coordinateMatrix G Phi).rank ≤ d ∧
    Module.finrank ℝ (affineSpan ℝ (Phi '' {rho : Algebra d | IsDensityMatrix rho})).direction ≤ d-1 := by
  rcases hClass with ⟨e, R, hR, rfl⟩ | ⟨e, F, hF, rfl⟩
  · refine S170bM_key G.positive G R _ (fun m => (hR m).1.isHermitian) (fun m => ?_) (S170bM_complete e)
    ext a b; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]
  · refine S170bM_key G.positive G _ F (fun m => ?_) (fun m => (hF.1 m).isHermitian) hF.2
    ext a b; simp [pureDensity, Matrix.conjTranspose_apply, mul_comm]

end
