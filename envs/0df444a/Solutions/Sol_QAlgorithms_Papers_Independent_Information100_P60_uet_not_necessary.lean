-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P60.uet_not_necessary
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:44:47.017355+00:00
-- url     : https://prove2.me/submissions/d7a23831-3cb9-45b9-8f22-f2c0fc57cd52

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P60

noncomputable section
open scoped Matrix ComplexConjugate ENNReal
open Filter Topology
open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P60

attribute [local instance] Classical.propDecidable Classical.decEq

lemma g53g_a2 : ((Real.sqrt 3 : ℝ) : ℂ) ^ 2 = 3 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

lemma g53g_omega : Complex.exp (2 * Real.pi * Complex.I / 3) =
    -1/2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I := by
  have h : (2 * Real.pi * Complex.I / 3 : ℂ) = ((2 * Real.pi / 3 : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hc : Real.cos (2 * Real.pi / 3) = -1/2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.cos_pi_sub, Real.cos_pi_div_three]; try norm_num
  have hs : Real.sin (2 * Real.pi / 3) = Real.sqrt 3 / 2 := by
    rw [show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub, Real.sin_pi_div_three]
  rw [hc, hs]; push_cast; ring

lemma g53g_expn (n : ℕ) : Complex.exp (2 * Real.pi * Complex.I * ((n : ℕ) : ℂ) / ((3 : ℕ) : ℂ)) =
    (-1/2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I) ^ n := by
  rw [← g53g_omega, ← Complex.exp_nat_mul]; congr 1; push_cast; ring

lemma g53g_sqrt3 : ((Real.sqrt ((3:ℕ) : ℝ) : ℝ) : ℂ) = ((Real.sqrt 3 : ℝ) : ℂ) := by norm_num

lemma g53g_inv : (((Real.sqrt 3 : ℝ) : ℂ))⁻¹ = ((Real.sqrt 3 : ℝ) : ℂ) / 3 := by
  have h := g53g_a2
  have hne : ((Real.sqrt 3 : ℝ) : ℂ) ≠ 0 := by
    intro h0; rw [h0] at h; norm_num at h
  field_simp; rw [← h]; try ring


def g53g_U0 : Mat (Fin 3) :=
  !![((Real.sqrt 3 : ℝ) : ℂ)/3, ((Real.sqrt 3 : ℝ) : ℂ)/3, ((Real.sqrt 3 : ℝ) : ℂ)/3;
     ((Real.sqrt 3 : ℝ) : ℂ)/3, (-1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/2*Complex.I)*((Real.sqrt 3 : ℝ) : ℂ)/3, (-1/2 - ((Real.sqrt 3 : ℝ) : ℂ)/2*Complex.I)*((Real.sqrt 3 : ℝ) : ℂ)/3;
     (-1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/2*Complex.I)*((Real.sqrt 3 : ℝ) : ℂ)/3, ((Real.sqrt 3 : ℝ) : ℂ)/3, (-1/2 - ((Real.sqrt 3 : ℝ) : ℂ)/2*Complex.I)*((Real.sqrt 3 : ℝ) : ℂ)/3]

lemma g53g_a3 : ((Real.sqrt 3 : ℝ) : ℂ)^3 = 3*((Real.sqrt 3 : ℝ) : ℂ) := by rw [pow_succ, g53g_a2]
lemma g53g_a4 : ((Real.sqrt 3 : ℝ) : ℂ)^4 = 9 := by rw [show (4:ℕ) = 2*2 from rfl, pow_mul, g53g_a2]; norm_num
lemma g53g_a5 : ((Real.sqrt 3 : ℝ) : ℂ)^5 = 9*((Real.sqrt 3 : ℝ) : ℂ) := by rw [pow_succ, g53g_a4]
lemma g53g_a6 : ((Real.sqrt 3 : ℝ) : ℂ)^6 = 27 := by rw [pow_succ, g53g_a5, mul_assoc, ← pow_two, g53g_a2]; norm_num
lemma g53g_I3 : Complex.I^3 = -Complex.I := by rw [pow_succ, Complex.I_sq]; ring
lemma g53g_I4 : Complex.I^4 = 1 := Complex.I_pow_four
lemma g53g_I5 : Complex.I^5 = Complex.I := by rw [pow_succ, g53g_I4]; ring
lemma g53g_I6 : Complex.I^6 = -1 := by rw [pow_succ, g53g_I5, Complex.I_mul_I]
lemma g53g_a7 : ((Real.sqrt 3 : ℝ) : ℂ)^7 = 27*((Real.sqrt 3 : ℝ) : ℂ) := by rw [pow_succ, g53g_a6]
lemma g53g_a8 : ((Real.sqrt 3 : ℝ) : ℂ)^8 = 81 := by rw [pow_succ, g53g_a7, mul_assoc, ← pow_two, g53g_a2]; norm_num


lemma g53g_Q : qftMatrix 3 = Matrix.of fun (i j : Fin 3) =>
    (-1/2 + ((Real.sqrt 3 : ℝ) : ℂ) / 2 * Complex.I) ^ ((i : ℕ) * (j : ℕ)) * (((Real.sqrt 3 : ℝ) : ℂ) / 3) := by
  ext i j
  rw [qftMatrix_apply, g53g_expn, g53g_sqrt3, div_eq_mul_inv, g53g_inv]; rfl

lemma g53g_U : counterU = g53g_U0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [counterU, phaseP, g53g_U0, Matrix.mul_apply, Fin.sum_univ_three, g53g_Q, g53g_omega] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_V0 : Mat (Fin 3) := !![1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/6*Complex.I, 1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/6*Complex.I, -((Real.sqrt 3 : ℝ) : ℂ)/3*Complex.I; 1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/6*Complex.I, -((Real.sqrt 3 : ℝ) : ℂ)/3*Complex.I, 1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/6*Complex.I; -1/2 + ((Real.sqrt 3 : ℝ) : ℂ)/6*Complex.I, -((Real.sqrt 3 : ℝ) : ℂ)/3*Complex.I, -((Real.sqrt 3 : ℝ) : ℂ)/3*Complex.I]

lemma g53g_V : counterV = g53g_V0 := by
  have hP2 : phaseP ^ 2 = Matrix.diagonal ![1, 1, -1/2 - ((Real.sqrt 3 : ℝ) : ℂ)/2*Complex.I] := by
    rw [phaseP, pow_two, Matrix.diagonal_mul_diagonal]
    congr 1; ext i; fin_cases i <;> simp [g53g_omega] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))
  have hU : phaseP * qftMatrix 3 = g53g_U0 := g53g_U
  rw [counterV, mul_assoc, hU, hP2]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g53g_V0, g53g_U0, Matrix.mul_apply, Fin.sum_univ_three, g53g_Q, Matrix.diagonal] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_A2M : Mat (Fin 3) := !![(1/1:ℂ)*1, (1/2:ℂ)*1 + (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (-1/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (1/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (2/1:ℂ)*1, 0; (-1/2:ℂ)*1 + (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, 0, (3/1:ℂ)*1]

lemma g53g_A2 : K1 ^ 2 = g53g_A2M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K1, g53g_A2M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_B2M : Mat (Fin 3) := !![(1/1:ℂ)*1, (-1/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (3/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (-1/2:ℂ)*1 + (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (4/1:ℂ)*1, 0; (3/2:ℂ)*1 + (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, 0, (5/1:ℂ)*1]

lemma g53g_B2 : K2 ^ 2 = g53g_B2M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [K2, g53g_B2M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_X1M : Mat (Fin 3) := !![(-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (3/2:ℂ)*1 + (3/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (-1/1:ℂ)*1 + (-3/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (-1/2:ℂ)*1 + (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (7/1:ℂ)*1, (-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (4/1:ℂ)*1 + (2/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (1/1:ℂ)*1, (15/1:ℂ)*1 + (1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I]

lemma g53g_X1 : g53g_A2M * g53g_B2M = g53g_X1M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g53g_A2M, g53g_B2M, g53g_X1M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_X2M : Mat (Fin 3) := !![(-5/1:ℂ)*1 + (-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (1/2:ℂ)*1 + (-3/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (4/1:ℂ)*1 + (4/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (-3/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (7/1:ℂ)*1 + (-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (6/1:ℂ)*1 + (1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (9/1:ℂ)*1 + (-7/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (16/1:ℂ)*1 + (1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (-15/1:ℂ)*1 + (2/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I]

lemma g53g_X2 : g53g_X1M * K1 = g53g_X2M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g53g_X1M, K1, g53g_X2M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_Y1M : Mat (Fin 3) := !![(1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (-1/2:ℂ)*1 + (-1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (4/1:ℂ)*1 + (-2/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I; (3/2:ℂ)*1 + (-3/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (7/1:ℂ)*1, (1/1:ℂ)*1; (-1/1:ℂ)*1 + (3/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I, (15/1:ℂ)*1 + (-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ)*Complex.I]

lemma g53g_Y1 : g53g_B2M * g53g_A2M = g53g_Y1M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g53g_B2M, g53g_A2M, g53g_Y1M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

def g53g_Y2M : Mat (Fin 3) := !![(3/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (-1/1:ℂ)*Complex.I, (-3/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (-5/2:ℂ)*Complex.I, (5/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (-5/1:ℂ)*Complex.I; (1/2:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (1/2:ℂ)*Complex.I, (-7/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (-1/1:ℂ)*Complex.I, (1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (4/1:ℂ)*Complex.I; (8/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (6/1:ℂ)*Complex.I, (-1/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (-18/1:ℂ)*Complex.I, (15/1:ℂ)*((Real.sqrt 3 : ℝ) : ℂ) + (2/1:ℂ)*Complex.I]

lemma g53g_Y2 : g53g_Y1M * K2 = g53g_Y2M := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [g53g_Y1M, K2, g53g_Y2M, pow_two, Matrix.mul_apply, Fin.sum_univ_three] <;>
    (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

lemma g53g_chi : chi K1 K2 = 24 * Complex.I := by
  rw [chi, g53g_A2, g53g_B2, g53g_X1, g53g_X2, g53g_Y1, g53g_Y2]
  simp [Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply, K1, K2, g53g_X2M, g53g_Y2M]
  (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf))

lemma g53g_chi_transpose (A B : Mat (Fin 3)) : chi A.transpose B.transpose = - chi A B := by
  have h1 : A.transpose ^ 2 * B.transpose ^ 2 * A.transpose * B.transpose =
      (B * A * (B ^ 2 * A ^ 2)).transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_pow, mul_assoc]
  have h2 : B.transpose ^ 2 * A.transpose ^ 2 * B.transpose * A.transpose =
      (A * B * (A ^ 2 * B ^ 2)).transpose := by
    simp only [Matrix.transpose_mul, Matrix.transpose_pow, mul_assoc]
  unfold chi
  rw [Matrix.trace_sub, Matrix.trace_sub, h1, h2, Matrix.trace_transpose, Matrix.trace_transpose,
    Matrix.trace_mul_comm (B * A), Matrix.trace_mul_comm (A * B)]
  simp only [mul_assoc]; ring

lemma g53g_chi_conj (A B S : Mat (Fin 3)) (hS : Sᴴ * S = 1) :
    chi (S * A * Sᴴ) (S * B * Sᴴ) = chi A B := by
  have hk : ∀ X : Mat (Fin 3), X * Sᴴ * S = X := by intro X; rw [mul_assoc, hS, mul_one]
  have e : ∀ X Y Z W : Mat (Fin 3),
      (S * X * Sᴴ) ^ 2 * (S * Y * Sᴴ) ^ 2 * (S * Z * Sᴴ) * (S * W * Sᴴ) =
        S * (X ^ 2 * Y ^ 2 * Z * W) * Sᴴ := by
    intro X Y Z W
    simp only [pow_two, ← mul_assoc, hk]
  have tr : ∀ X : Mat (Fin 3), (S * X * Sᴴ).trace = X.trace := by
    intro X; rw [Matrix.trace_mul_comm, ← mul_assoc, hS, one_mul]
  unfold chi
  rw [e, e, ← Matrix.sub_mul, ← Matrix.mul_sub, tr]


lemma g53g_u1 : g53g_U0 * g53g_U0ᴴ = 1 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))
lemma g53g_u2 : g53g_U0ᴴ * g53g_U0 = 1 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))
lemma g53g_v1 : g53g_V0 * g53g_V0ᴴ = 1 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))
lemma g53g_v2 : g53g_V0ᴴ * g53g_V0 = 1 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))
lemma g53g_c1 : K1.transpose + g53g_U0 * K1 * g53g_U0ᴴ + g53g_V0 * K1 * g53g_V0ᴴ = 0 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))
lemma g53g_c2 : K2.transpose + g53g_U0 * K2 * g53g_U0ᴴ + g53g_V0 * K2 * g53g_V0ᴴ = 0 := by
  (ext i j; fin_cases i <;> fin_cases j <;>
    simp [g53g_U0, g53g_V0, K1, K2, Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply,
      Matrix.one_apply, map_ofNat, map_div₀, map_inv₀, Matrix.vecMul, Matrix.mulVec, dotProduct] <;> (ring_nf; (try simp only [g53g_a2, g53g_a3, g53g_a4, g53g_a5, g53g_a6, g53g_a7, g53g_a8, Complex.I_sq, g53g_I3, g53g_I4, g53g_I5, g53g_I6]); (try ring_nf)))

theorem solution :
    K1.IsHermitian ∧ K2.IsHermitian ∧ K1.trace = 0 ∧ K2.trace = 0 ∧
    counterU * counterUᴴ = 1 ∧ counterUᴴ * counterU = 1 ∧ counterV * counterVᴴ = 1 ∧ counterVᴴ * counterV = 1 ∧
    (∀ M ∈ ({K1, K2} : Set (Mat (Fin 3))), M.transpose + counterU * M * counterUᴴ + counterV * M * counterVᴴ = 0) ∧
    chi K1 K2 = 24 * Complex.I ∧ ¬ JointUET K1 K2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, g53g_chi, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [K1, Complex.ext_iff]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [K2, Complex.ext_iff]
  · simp [K1, Matrix.trace, Fin.sum_univ_three]
  · simp [K2, Matrix.trace, Fin.sum_univ_three]
  · rw [g53g_U]; exact g53g_u1
  · rw [g53g_U]; exact g53g_u2
  · rw [g53g_V]; exact g53g_v1
  · rw [g53g_V]; exact g53g_v2
  · intro M hM
    rcases hM with rfl | hM
    · rw [g53g_U, g53g_V]; exact g53g_c1
    · rw [Set.mem_singleton_iff] at hM; subst hM; rw [g53g_U, g53g_V]; exact g53g_c2
  · rintro ⟨S, hA, hB⟩
    have hS : (S : Mat (Fin 3))ᴴ * (S : Mat (Fin 3)) = 1 := by
      have := (Matrix.mem_unitaryGroup_iff').mp S.2
      simpa [Matrix.star_eq_conjTranspose] using this
    have h1 := g53g_chi_conj K1 K2 _ hS
    rw [hA, hB, g53g_chi_transpose, g53g_chi] at h1
    have h2 : (2 : ℂ) * (24 * Complex.I) = 0 := by linear_combination -h1
    simp at h2
