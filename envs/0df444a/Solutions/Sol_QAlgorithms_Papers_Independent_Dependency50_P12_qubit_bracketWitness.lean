-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P12.qubit_bracketWitness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:59:31.092463+00:00
-- url     : https://prove2.me/submissions/2a085d20-cbe0-409d-98e8-1cf395cad590

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P12

noncomputable section

open scoped Matrix ComplexOrder Matrix.Norms.Frobenius

open Set

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P12

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] Classical.propDecidable Classical.decEq

open Coordinates

open QAlgorithms.Papers.Independent.Information100

attribute [local instance] QAlgorithms.Papers.Independent.Dependency50.P12.inheritedSubalgebraTopologicalAddGroup

lemma g53g_s0 : sigma 0 = !![0, 1; 1, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma, QAlgorithms.QubitChannels.sigma, pauliX]
lemma g53g_s1 : sigma 1 = !![0, -Complex.I; Complex.I, 0] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma, QAlgorithms.QubitChannels.sigma, pauliY]
lemma g53g_s2 : sigma 2 = !![1, 0; 0, -1] := by
  ext i j; fin_cases i <;> fin_cases j <;>
    simp [sigma, QAlgorithms.QubitChannels.sigma, pauliZ]

lemma g53g_apply (t : Super 2) (X : P59.Operator 2) (i j : Fin 2) :
    P26.applyMap t X i j = ∑ p : Fin 2 × Fin 2, t (i, j) p * X p.1 p.2 := by
  simp [P26.applyMap, QAlgorithms.act, Matrix.mulVec, dotProduct]

def g53g_B0 : Super 2 := fun p q =>
  if q.1 = q.2 then (if p = (0, 0) then -1 else if p = (1, 1) then 1 else 0) else 0

lemma g53g_B : (⁅dissipatorMap sigmaMinus, dissipatorMap (sigma 0)⁆ : Super 2) = g53g_B0 := by
  rw [Ring.lie_def, g53g_s0]
  ext ⟨a, b⟩ ⟨c, d⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [g53g_B0, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two, dissipatorMap,
      superOfAction, P59.dissipator, sigmaMinus, Matrix.single_apply, Matrix.conjTranspose_apply, Matrix.vecMul, dotProduct] <;>
    norm_num

lemma g53g_applyB (X : P59.Operator 2) :
    P26.applyMap g53g_B0 X = !![-(X 0 0 + X 1 1), 0; 0, X 0 0 + X 1 1] := by
  ext i j
  rw [g53g_apply]
  fin_cases i <;> fin_cases j <;> simp [g53g_B0, Fintype.sum_prod_type, Fin.sum_univ_two]

lemma g53g_applyD (L X : P59.Operator 2) :
    P26.applyMap (dissipatorMap L) X = P59.dissipator L X := by
  ext i j
  rw [g53g_apply]
  fin_cases i <;> fin_cases j <;>
    simp [dissipatorMap, superOfAction, P59.dissipator, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.single_apply, Fintype.sum_prod_type, Matrix.conjTranspose_apply] <;> ring

lemma g53g_I3 : Complex.I^3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring

lemma g53g_r2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num
lemma g53g_ri2 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 2 = 1/2 := by
  rw [inv_pow, g53g_r2]; norm_num
lemma g53g_ri4 : (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) ^ 4 = 1/4 := by
  rw [show (4:ℕ) = 2*2 from rfl, pow_mul, g53g_ri2]; norm_num

lemma g53g_physX : P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap (sigma 0))) := by
  refine ⟨0, Matrix.diagonal ![2, 0, 0], by simp, ?_, ?_⟩
  · rw [Matrix.posSemidef_diagonal_iff]; intro i; fin_cases i <;> simp
  · funext X
    rw [g53g_applyD]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [P59.kossakowskiAction, P59.coherent, P59.dissipator, pauliBasis, g53g_s0, g53g_s1, g53g_s2,
        Fin.sum_univ_succ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Matrix.diagonal_apply, Matrix.vecMul, dotProduct] <;>
      (ring_nf; (try simp only [g53g_ri2, g53g_ri4, g53g_r2, Complex.I_sq, g53g_I3, Complex.I_pow_four]); (try ring_nf))

lemma g53g_physM : P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap sigmaMinus)) := by
  let c : Fin 3 → ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • ![1, -Complex.I, 0]
  refine ⟨0, Matrix.vecMulVec c (star c), by simp, Matrix.posSemidef_vecMulVec_self_star c, ?_⟩
  funext X
  rw [g53g_applyD]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [c, P59.kossakowskiAction, P59.coherent, P59.dissipator, pauliBasis, g53g_s0, g53g_s1, g53g_s2,
      sigmaMinus, Matrix.single_apply,
      Fin.sum_univ_succ, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
      Matrix.vecMulVec_apply, Matrix.vecMul, dotProduct] <;>
    (ring_nf; (try simp only [g53g_ri2, g53g_ri4, g53g_r2, Complex.I_sq, g53g_I3, Complex.I_pow_four]); (try ring_nf))

lemma g53g_notPhys : ¬ P59.IsPhysicalAction pauliBasis (P26.applyMap g53g_B0) := by
  rintro ⟨H, K, hH, hK, hEq⟩
  have hE : (Matrix.single 1 1 1 : P59.Operator 2) = !![0, 0; 0, 1] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.single_apply]
  have h1 := congrFun (congrFun (congrFun hEq (!![0, 0; 0, 1])) 0) 0
  rw [g53g_applyB] at h1
  let x : Fin 3 → ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • ![1, Complex.I, 0]
  have h2 := hK.dotProduct_mulVec_nonneg x
  have h3 : star x ⬝ᵥ (K *ᵥ x) = -1 := by
    have e : star x ⬝ᵥ (K *ᵥ x) = P59.kossakowskiAction pauliBasis H K (!![0, 0; 0, 1]) 0 0 := by
      simp [x, P59.kossakowskiAction, P59.coherent, pauliBasis, g53g_s0, g53g_s1, g53g_s2,
        Matrix.single_apply, Fin.sum_univ_succ, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.conjTranspose_apply, Matrix.mulVec, Matrix.vecMul, dotProduct, Matrix.vecHead,
        Matrix.vecTail]
      ring_nf; (try simp only [g53g_ri2, g53g_ri4, g53g_r2, Complex.I_sq, g53g_I3, Complex.I_pow_four]); (try ring_nf)
    rw [e, ← h1]; simp
  rw [h3] at h2
  norm_num at h2

lemma g53g_Q : blochQ g53g_B0 = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [blochQ, g53g_applyB, g53g_s0, g53g_s1, g53g_s2, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply]

lemma g53g_bB : blochB g53g_B0 = ![0, 0, -2] := by
  ext i
  fin_cases i <;>
    simp [blochB, g53g_applyB, g53g_s0, g53g_s1, g53g_s2, Matrix.trace, Fin.sum_univ_two, Matrix.mul_apply] <;>
    norm_num

lemma g53g_K : pauliKossakowskiMatrix g53g_B0 = !![0, Complex.I, 0; -Complex.I, 0, 0; 0, 0, 0] := by
  unfold pauliKossakowskiMatrix
  rw [g53g_Q, g53g_bB]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [P59.rotationGenerator] <;> ring

lemma g53g_charpoly : (!![0, Complex.I, 0; -Complex.I, 0, 0; 0, 0, 0] : Matrix (Fin 3) (Fin 3) ℂ).charpoly =
    Polynomial.X * (Polynomial.X - 1) * (Polynomial.X + 1) := by
  rw [Matrix.charpoly, Matrix.det_fin_three]
  simp [Matrix.charmatrix_apply, Matrix.diagonal_apply]
  have : (Polynomial.C Complex.I) * (Polynomial.C Complex.I) = -1 := by
    rw [← Polynomial.C_mul, Complex.I_mul_I]; simp
  linear_combination Polynomial.X * this

theorem solution :
    P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap sigmaMinus)) ∧
    P59.IsPhysicalAction pauliBasis (P26.applyMap (dissipatorMap (sigma 0))) ∧
    (let B := ⁅dissipatorMap sigmaMinus, dissipatorMap (sigma 0)⁆
     B ≠ 0 ∧ blochQ B = 0 ∧ blochB B = ![0, 0, -2] ∧
     (pauliKossakowskiMatrix B).charpoly = Polynomial.X * (Polynomial.X - 1) * (Polynomial.X + 1) ∧
     ¬ P59.IsPhysicalAction pauliBasis (P26.applyMap B)) := by
  refine ⟨g53g_physM, g53g_physX, ?_⟩
  intro B
  have hB : B = g53g_B0 := g53g_B
  rw [hB]
  refine ⟨?_, g53g_Q, g53g_bB, ?_, g53g_notPhys⟩
  · intro h
    have := congrFun (congrFun h (0, 0)) (0, 0)
    simp [g53g_B0] at this
  · rw [g53g_K]; exact g53g_charpoly
