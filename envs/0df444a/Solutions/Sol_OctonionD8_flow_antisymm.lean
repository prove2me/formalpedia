-- Prove2me | solution 1 for OctonionD8.flow_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @ShapeZero
-- created : 2026-09-27T05:27:39.905387+00:00
-- url     : https://prove2.me/submissions/c4366447-cc55-41e8-9577-6016c92c0a01

import Mathlib
import Definitions.Def_OctonionD8_blocks
namespace OctonionD8Sol

open OctonionD8 Polynomial

def Tlit : Fin 8 → Fin 8 → Fin 8 → ℤ := ![![![1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 0, 0, 1]], ![![0, 1, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, -1, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0]], ![![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 0, 0, 0, -1, 0]], ![![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 0, -1, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, -1, 0, 0]], ![![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, -1, 0], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 1, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, 0, 0, 0, -1], ![0, 0, 0, 0, 1, 0, 0, 0], ![0, 0, 0, -1, 0, 0, 0, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 1, 0, 0, 0, 0, 0]], ![![0, 0, 0, 0, 0, 0, 0, 1], ![0, 0, 0, 1, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 1, 0], ![0, -1, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, -1, 0, 0, 0, 0, 0], ![-1, 0, 0, 0, 0, 0, 0, 0]]]

set_option maxRecDepth 100000 in
theorem octTable_eq : ∀ i j k, octTable i j k = Tlit i j k := by decide

theorem omul_eq (p q : Fin 8 → ℝ) : omul p q =
  ![p 0*q 0 - p 1*q 1 - p 2*q 2 - p 3*q 3 - p 4*q 4 - p 5*q 5 - p 6*q 6 - p 7*q 7,
    p 0*q 1 + p 1*q 0 + p 2*q 4 + p 3*q 7 - p 4*q 2 + p 5*q 6 - p 6*q 5 - p 7*q 3,
    p 0*q 2 - p 1*q 4 + p 2*q 0 + p 3*q 5 + p 4*q 1 - p 5*q 3 + p 6*q 7 - p 7*q 6,
    p 0*q 3 - p 1*q 7 - p 2*q 5 + p 3*q 0 + p 4*q 6 + p 5*q 2 - p 6*q 4 + p 7*q 1,
    p 0*q 4 + p 1*q 2 - p 2*q 1 - p 3*q 6 + p 4*q 0 + p 5*q 7 + p 6*q 3 - p 7*q 5,
    p 0*q 5 - p 1*q 6 + p 2*q 3 - p 3*q 2 - p 4*q 7 + p 5*q 0 + p 6*q 1 + p 7*q 4,
    p 0*q 6 + p 1*q 5 - p 2*q 7 + p 3*q 4 - p 4*q 3 - p 5*q 1 + p 6*q 0 + p 7*q 2,
    p 0*q 7 + p 1*q 3 + p 2*q 6 - p 3*q 1 + p 4*q 5 - p 5*q 4 - p 6*q 2 + p 7*q 0] := by
  funext k
  fin_cases k <;>
    simp [omul, Fin.sum_univ_eight, octTable_eq, Tlit] <;> ring

theorem flowMat_eq (c s : ℝ) : flowMat c s = !![0, -c - 1, -s, 0, 0, 0, 0, 0;
    c + 1, 0, 0, 0, s, 0, 0, 0;
    s, 0, 0, 0, 1 - c, 0, 0, 0;
    0, 0, 0, 0, 0, -s, 0, 1 - c;
    0, -s, c - 1, 0, 0, 0, 0, 0;
    0, 0, 0, s, 0, 0, 1 - c, 0;
    0, 0, 0, 0, 0, c - 1, 0, -s;
    0, 0, 0, c - 1, 0, 0, s, 0] := by
  ext k j
  fin_cases k <;> fin_cases j <;>
    simp [flowMat, Rmat, Lmat, omul_eq] <;> ring

theorem norm_mul (p q : Fin 8 → ℝ) :
    ∑ k, (omul p q k) ^ 2 = (∑ i, p i ^ 2) * (∑ j, q j ^ 2) := by
  simp only [omul_eq, Fin.sum_univ_eight]
  simp
  ring

theorem flow_antisymm (c s : ℝ) : (flowMat c s).transpose = -flowMat c s := by
  rw [flowMat_eq]
  ext k j
  fin_cases k <;> fin_cases j <;> simp <;> ring


set_option maxHeartbeats 4000000 in
theorem flow_sq (c s : ℝ) : flowMat c s ^ 2 = !![-c^2 - 2*c - s^2 - 1, 0, 0, 0, -2*s, 0, 0, 0;
    0, -c^2 - 2*c - s^2 - 1, -2*s, 0, 0, 0, 0, 0;
    0, -2*s, -c^2 + 2*c - s^2 - 1, 0, 0, 0, 0, 0;
    0, 0, 0, -c^2 + 2*c - s^2 - 1, 0, 0, 0, 0;
    -2*s, 0, 0, 0, -c^2 + 2*c - s^2 - 1, 0, 0, 0;
    0, 0, 0, 0, 0, -c^2 + 2*c - s^2 - 1, 0, 0;
    0, 0, 0, 0, 0, 0, -c^2 + 2*c - s^2 - 1, 0;
    0, 0, 0, 0, 0, 0, 0, -c^2 + 2*c - s^2 - 1] := by
  rw [sq, flowMat_eq]; ext k j
  fin_cases k <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_eight] <;> ring

set_option maxHeartbeats 4000000 in
theorem flow_Q1 (c s : ℝ) :
    flowMat c s * (flowMat c s ^ 2 + (4 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) =
      !![0, c^3 + 3*c^2 + c*s^2 - c + 3*s^2 - 3, c^2*s + s^3 - s, 0, 0, 0, 0, 0;
    -c^3 - 3*c^2 - c*s^2 + c - 3*s^2 + 3, 0, 0, 0, -c^2*s - s^3 + s, 0, 0, 0;
    -c^2*s - s^3 + s, 0, 0, 0, c^3 - 3*c^2 + c*s^2 - c - 3*s^2 + 3, 0, 0, 0;
    0, 0, 0, 0, 0, c^2*s - 2*c*s + s^3 - 3*s, 0, c^3 - 3*c^2 + c*s^2 - c - s^2 + 3;
    0, c^2*s + s^3 - s, -c^3 + 3*c^2 - c*s^2 + c + 3*s^2 - 3, 0, 0, 0, 0, 0;
    0, 0, 0, -c^2*s + 2*c*s - s^3 + 3*s, 0, 0, c^3 - 3*c^2 + c*s^2 - c - s^2 + 3, 0;
    0, 0, 0, 0, 0, -c^3 + 3*c^2 - c*s^2 + c + s^2 - 3, 0, c^2*s - 2*c*s + s^3 - 3*s;
    0, 0, 0, -c^3 + 3*c^2 - c*s^2 + c + s^2 - 3, 0, 0, -c^2*s + 2*c*s - s^3 + 3*s, 0] := by
  rw [flow_sq, flowMat_eq]; ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Matrix.one_apply] <;> ring

set_option maxHeartbeats 4000000 in
theorem flow_F (c s : ℝ) :
    flowMat c s * (flowMat c s ^ 2 + (4 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) *
      (flowMat c s ^ 2 + (2 - 2 * c) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) =
      (c ^ 2 + s ^ 2 - 1) • !![0, -c^3 - 7*c^2 - c*s^2 - 11*c - 5*s^2 + 3, -c^2*s - 2*c*s - s^3 - 5*s, 0, 0, 0, 0, 0;
    c^3 + 7*c^2 + c*s^2 + 11*c + 5*s^2 - 3, 0, 0, 0, c^2*s + 2*c*s + s^3 + 5*s, 0, 0, 0;
    c^2*s + 2*c*s + s^3 + 5*s, 0, 0, 0, -c^3 + 3*c^2 - c*s^2 + c + 5*s^2 - 3, 0, 0, 0;
    0, 0, 0, 0, 0, -c^2*s + 2*c*s - s^3 + 3*s, 0, -c^3 + 3*c^2 - c*s^2 + c + s^2 - 3;
    0, -c^2*s - 2*c*s - s^3 - 5*s, c^3 - 3*c^2 + c*s^2 - c - 5*s^2 + 3, 0, 0, 0, 0, 0;
    0, 0, 0, c^2*s - 2*c*s + s^3 - 3*s, 0, 0, -c^3 + 3*c^2 - c*s^2 + c + s^2 - 3, 0;
    0, 0, 0, 0, 0, c^3 - 3*c^2 + c*s^2 - c - s^2 + 3, 0, -c^2*s + 2*c*s - s^3 + 3*s;
    0, 0, 0, c^3 - 3*c^2 + c*s^2 - c - s^2 + 3, 0, 0, c^2*s - 2*c*s + s^3 - 3*s, 0] := by
  rw [flow_Q1, flow_sq]; ext k j
  fin_cases k <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_eight, Matrix.one_apply] <;> ring

theorem flow_annihilating (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    flowMat c s * (flowMat c s ^ 2 + (4 : ℝ) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) *
      (flowMat c s ^ 2 + (2 - 2 * c) • (1 : Matrix (Fin 8) (Fin 8) ℝ)) = 0 := by
  rw [flow_F, show c ^ 2 + s ^ 2 - 1 = 0 by linarith, zero_smul]

theorem flow_block_diag (c s : ℝ) :
    Matrix.reindex blockEquiv blockEquiv (flowMat c s) =
      Matrix.fromBlocks (blockA c s) 0 0 (blockB c s) := by
  rw [flowMat_eq]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [blockEquiv, blockA, blockB]

theorem charpoly_blockA_aux (c s : ℝ) : (blockA c s).charpoly =
    X ^ 2 * (X ^ 2 + 4) + C (c ^ 2 + s ^ 2 - 1) * (C c^2 + C s^2 + 2*X^2 - 1) := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.charmatrix_apply, blockA,
    Matrix.submatrix_apply, Fin.succAbove, Matrix.diagonal_apply]
  ring

theorem charpoly_blockB_aux (c s : ℝ) : (blockB c s).charpoly =
    (X ^ 2 + C (2 - 2 * c)) ^ 2 + C (c ^ 2 + s ^ 2 - 1) * (C c^2 - 4*C c + C s^2 + 2*X^2 + 3) := by
  rw [Matrix.charpoly, Matrix.det_succ_row_zero]
  simp [Fin.sum_univ_succ, Matrix.det_fin_three, Matrix.charmatrix_apply, blockB,
    Matrix.submatrix_apply, Fin.succAbove, Matrix.diagonal_apply]
  simp only [show (C (2 : ℝ) : ℝ[X]) = 2 from map_ofNat C 2]
  ring

theorem charpoly_blockA (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (blockA c s).charpoly = X ^ 2 * (X ^ 2 + 4) := by
  rw [charpoly_blockA_aux, show c ^ 2 + s ^ 2 - 1 = 0 by linarith, C_0]
  ring

theorem charpoly_blockB (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (blockB c s).charpoly = (X ^ 2 + C (2 - 2 * c)) ^ 2 := by
  rw [charpoly_blockB_aux, show c ^ 2 + s ^ 2 - 1 = 0 by linarith, C_0]
  ring

theorem flow_charpoly (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) :
    (flowMat c s).charpoly = X ^ 2 * (X ^ 2 + 4) * (X ^ 2 + C (2 - 2 * c)) ^ 2 := by
  rw [← Matrix.charpoly_reindex blockEquiv (flowMat c s), flow_block_diag,
    Matrix.charpoly_fromBlocks_zero₁₂, charpoly_blockA c s h, charpoly_blockB c s h]

theorem flow_eigenvalues (θ : ℝ) (hθ₀ : 0 < θ) (hθ₁ : θ < Real.pi) :
    ((flowMat (Real.cos θ) (Real.sin θ)).charpoly.map (algebraMap ℝ ℂ)).roots =
      {0, 0, 2 * Complex.I, -(2 * Complex.I),
        2 * Complex.I * (Real.sin (θ / 2) : ℂ), 2 * Complex.I * (Real.sin (θ / 2) : ℂ),
        -(2 * Complex.I * (Real.sin (θ / 2) : ℂ)), -(2 * Complex.I * (Real.sin (θ / 2) : ℂ))} ∧
      0 < Real.sin (θ / 2) ∧ Real.sin (θ / 2) < 1 := by
  have hcs : Real.cos θ ^ 2 + Real.sin θ ^ 2 = 1 := Real.cos_sq_add_sin_sq θ
  have hcos : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h2 := Real.cos_two_mul (θ / 2)
    have h3 := Real.sin_sq_add_cos_sq (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [flow_charpoly _ _ hcs]
    set w : ℂ := 2 * Complex.I * (Real.sin (θ / 2) : ℂ) with hw
    have e1 : (X - C (2 * Complex.I)) * (X - C (-(2 * Complex.I))) = (X ^ 2 + 4 : ℂ[X]) := by
      have hI : (2 * Complex.I) ^ 2 = (-4 : ℂ) := by
        rw [mul_pow, Complex.I_sq]; norm_num
      calc (X - C (2 * Complex.I)) * (X - C (-(2 * Complex.I)))
          = X ^ 2 - C ((2 * Complex.I) ^ 2) := by simp only [map_neg, map_pow]; ring
        _ = X ^ 2 + 4 := by rw [hI, map_neg, map_ofNat C 4]; ring
    have e2 : (X - C w) * (X - C (-w)) =
        (X ^ 2 + C (((2 - 2 * Real.cos θ : ℝ)) : ℂ) : ℂ[X]) := by
      have hW : w ^ 2 = -(((2 - 2 * Real.cos θ : ℝ)) : ℂ) := by
        rw [hw, hcos]; push_cast; rw [mul_pow, mul_pow, Complex.I_sq]; ring
      calc (X - C w) * (X - C (-w)) = X ^ 2 - C (w ^ 2) := by
            simp only [map_neg, map_pow]; ring
        _ = _ := by rw [hW, map_neg]; ring
    have hprod : (Polynomial.map (algebraMap ℝ ℂ)
        (X ^ 2 * (X ^ 2 + 4) * (X ^ 2 + C (2 - 2 * Real.cos θ)) ^ 2)) =
        (({0, 0, 2 * Complex.I, -(2 * Complex.I), w, w, -w, -w} : Multiset ℂ).map
          (fun a => X - C a)).prod := by
      simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton,
        Multiset.prod_cons, Multiset.prod_singleton, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_add, Polynomial.map_X, Polynomial.map_C, Polynomial.map_ofNat, map_zero,
        sub_zero]
      rw [show (algebraMap ℝ ℂ) (2 - 2 * Real.cos θ) = (((2 - 2 * Real.cos θ : ℝ)) : ℂ) from rfl,
        ← e1, ← e2]
      ring
    rw [hprod, Polynomial.roots_multiset_prod_X_sub_C]
  · apply Real.sin_pos_of_pos_of_lt_pi <;> linarith
  · have : Real.sin (θ / 2) < Real.sin (Real.pi / 2) :=
      Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) (le_refl _) (by linarith)
    rwa [Real.sin_pi_div_two] at this

end OctonionD8Sol

open OctonionD8 Polynomial

theorem solution (c s : ℝ) : (flowMat c s).transpose = -flowMat c s := by
  apply OctonionD8Sol.flow_antisymm <;> assumption
