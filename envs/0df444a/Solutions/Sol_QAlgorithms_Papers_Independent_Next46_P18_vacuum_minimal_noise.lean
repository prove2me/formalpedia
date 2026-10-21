-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Next46.P18.vacuum_minimal_noise
-- status  : ACCEPTED   (prove)
-- author  : @Imine
-- created : 2026-10-21T03:08:25.109674+00:00
-- url     : https://prove2.me/submissions/b47bae4e-2c3b-4ee5-be93-7660ddf1edf5

import Definitions.Def_QAlgorithms_Papers_Independent_Next46_P18
import Theorems.Thm_QAlgorithms_Papers_Independent_Next46_P18_squeeze_projection_posSemidef

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology BigOperators ComplexOrder BoundedContinuousFunction Matrix
open QAlgorithms.RealRegisters (Hilbert)
open QAlgorithms.Papers.Independent.Claimed50.P35 (physicalCommutationMatrix)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex quantumCovariance interleavedSymplecticForm)
open QAlgorithms.Papers.Independent.Next46.P18

attribute [local instance] Classical.propDecidable Classical.decEq
attribute [local instance] IsStarNormal.instContinuousFunctionalCalculus

private lemma quantumCovariance_one :
    quantumCovariance (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ) := by
  have h := squeeze_projection_posSemidef (s := 1)
    (0 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)
    (0 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)
    (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)
    (by simp) (by simp) (by simp) (by simp) (by simp) (1) (by norm_num)
  simpa [quantumCovariance, interleavedSymplecticForm] using h

private lemma vacuum_minimal_noise_aux :
    MinimalNoise ((1 / 2 : ℝ) •
      (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) := by
  unfold MinimalNoise
  constructor
  · simpa [smul_smul] using quantumCovariance_one
  · intro beta hA hB
    let a := beta (0, 0) (0, 0)
    let b := beta (0, 0) (0, 1)
    let d := beta (0, 1) (0, 1)
    have hβsym : beta.transpose = beta := by
      have hT : (((1 / 2 : ℝ) •
          (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) - beta).transpose =
          ((1 / 2 : ℝ) • (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) - beta := by
        simpa [Matrix.IsSymm] using (Matrix.isHermitian_iff_isSymm.mp hB.isHermitian)
      have hαT : (((1 / 2 : ℝ) •
          (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ))).transpose =
          ((1 / 2 : ℝ) • (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) := by simp
      have h1 : ((1 / 2 : ℝ) •
          (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) - beta.transpose =
          ((1 / 2 : ℝ) • (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) - beta := by
        simpa [Matrix.transpose_sub, hαT] using hT
      exact sub_right_injective h1
    have hβ10 : beta (0, 1) (0, 0) = b := by
      have h := congrFun (congrFun hβsym (0, 1)) (0, 0)
      simpa [b, Matrix.transpose_apply] using h.symm
    unfold quantumCovariance at hA
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hA
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at hB
    have hq : 0 ≤ 2 * a := by
      have h := (Complex.nonneg_iff.mp (hA.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 1 else 0))).1
      simpa [a, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
        using h
    have hp : 0 ≤ 2 * d := by
      have h := (Complex.nonneg_iff.mp (hA.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 0 else 1))).1
      simpa [d, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
        using h
    have hdiag : 0 ≤ 2 * a + 2 * d - 2 := by
      have h := (Complex.nonneg_iff.mp (hA.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 1 else Complex.I))).1
      simp [a, d, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
        interleavedSymplecticForm] at h
      linarith
    have hBq : 0 ≤ 1 / 2 - a := by
      have h := hB.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 1 else 0)
      simpa [a, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
        using h
    have hBp : 0 ≤ 1 / 2 - d := by
      have h := hB.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 0 else 1)
      simpa [d, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two]
        using h
    have hBplus : 0 ≤ 1 - a - d - 2 * b := by
      have h := hB.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 1 else 1)
      simp [a, d, b, hβ10, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two] at h
      linarith
    have hBminus : 0 ≤ 1 - a - d + 2 * b := by
      have h := hB.2 (fun i : QuadratureIndex 1 => if i.2 = 0 then 1 else -1)
      simp [a, d, b, hβ10, dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two] at h
      linarith
    have haeq : a = 1 / 2 := by nlinarith
    have hdeq : d = 1 / 2 := by nlinarith
    have hbeq : b = 0 := by nlinarith
    ext i j
    obtain ⟨i1, i2⟩ := i
    obtain ⟨j1, j2⟩ := j
    fin_cases i1 <;> fin_cases j1 <;> fin_cases i2 <;> fin_cases j2 <;>
      simp [a, b, d, hβ10, haeq, hdeq, hbeq]



theorem solution :
    MinimalNoise ((1 / 2 : ℝ) •
      (1 : Matrix (QuadratureIndex 1) (QuadratureIndex 1) ℝ)) :=
  vacuum_minimal_noise_aux

end
